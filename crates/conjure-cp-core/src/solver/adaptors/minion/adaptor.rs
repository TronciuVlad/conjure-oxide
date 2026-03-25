use regex::Regex;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, LazyLock, Mutex, OnceLock};
use uniplate::Uniplate;
use ustr::Ustr;

use minion_ast::Model as MinionModel;
use minion_sys::ast as minion_ast;
use minion_sys::error::MinionError;
use minion_sys::{
    add_aux_var_during_search, add_constraint_during_search, get_from_table, run_minion,
};

use crate::Model as ConjureModel;
use crate::ast::{
    self as conjure_ast, Atom, Expression, GroundDomain, Literal, Metadata, Moo, Name,
    eval_constant, run_partial_evaluator,
};
use crate::rule_engine::rewrite_model_with_configured_rewriter;
use crate::settings::{SolverFamily, current_rewriter};
use crate::solver::SolverCallback;
use crate::solver::SolverMutCallback;
use crate::stats::SolverStats;

use crate::solver::SearchComplete::{HasSolutions, NoSolutions};
use crate::solver::SearchIncomplete::UserTerminated;
use crate::solver::SearchStatus::{Complete, Incomplete};
use crate::solver::SolveSuccess;
use crate::solver::SolverAdaptor;
use crate::solver::SolverError;
use crate::solver::SolverError::{OpNotImplemented, Runtime, RuntimeNotImplemented};
use crate::solver::private;

use super::parse_model::model_to_minion;

/// A [SolverAdaptor] for interacting with Minion.
///
/// This adaptor uses the `minion_sys` crate to talk to Minion over FFI.
pub struct Minion {
    __non_constructable: private::Internal,
    model: Option<MinionModel>,
    dominance_expression: Option<Expression>,
    dominance_model_template: Option<ConjureModel>,
}

static MINION_LOCK: Mutex<()> = Mutex::new(());
static USER_CALLBACK: OnceLock<Mutex<SolverCallback>> = OnceLock::new();
static ANY_SOLUTIONS: AtomicBool = AtomicBool::new(false);
static USER_TERMINATED: AtomicBool = AtomicBool::new(false);
static SOLUTION_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn parse_name(minion_name: &str) -> Name {
    static MACHINE_NAME_RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"__conjure_machine_name_([0-9]+)").unwrap());
    static REPRESENTED_NAME_RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"__conjure_represented_name__(.*)__(.*)___(.*)").unwrap());

    if let Some(caps) = MACHINE_NAME_RE.captures(minion_name) {
        conjure_ast::Name::Machine(caps[1].parse::<i32>().unwrap())
    } else if let Some(caps) = REPRESENTED_NAME_RE.captures(minion_name) {
        conjure_ast::Name::Represented(Box::new((
            parse_name(&caps[1]),
            Ustr::from(&caps[2]),
            Ustr::from(&caps[3]),
        )))
    } else {
        conjure_ast::Name::User(Ustr::from(minion_name))
    }
}

#[allow(clippy::unwrap_used)]
fn minion_sys_callback(solutions: HashMap<minion_ast::VarName, minion_ast::Constant>) -> bool {
    ANY_SOLUTIONS.store(true, Ordering::SeqCst);
    let callback = USER_CALLBACK
        .get_or_init(|| Mutex::new(Box::new(|x| true)))
        .lock()
        .unwrap();

    let mut conjure_solutions: HashMap<conjure_ast::Name, conjure_ast::Literal> = HashMap::new();
    for (minion_name, minion_const) in solutions.into_iter() {
        let conjure_const = match minion_const {
            minion_ast::Constant::Bool(x) => conjure_ast::Literal::Bool(x),
            minion_ast::Constant::Integer(x) => conjure_ast::Literal::Int(x),
            _ => todo!(),
        };

        let conjure_name = parse_name(&minion_name);
        conjure_solutions.insert(conjure_name, conjure_const);
    }

    let continue_search = (**callback)(conjure_solutions);
    if !continue_search {
        USER_TERMINATED.store(true, Ordering::SeqCst);
    }

    continue_search
}

impl private::Sealed for Minion {}

fn sub_in_solution_into_current_refs(
    expr: &Expression,
    solution: &HashMap<Name, Literal>,
) -> Option<Expression> {
    match expr {
        Expression::Atomic(_, Atom::Reference(reference)) => {
            let var_name = reference.name();
            let value = solution.get(&var_name)?;
            let value = if let Some(domain) = reference.resolved_domain() {
                if domain.as_ref() == &GroundDomain::Bool {
                    match value {
                        Literal::Bool(x) => Literal::Bool(*x),
                        Literal::Int(1) => Literal::Bool(true),
                        Literal::Int(0) => Literal::Bool(false),
                        _ => return None,
                    }
                } else {
                    value.clone()
                }
            } else {
                value.clone()
            };

            Some(Expression::Atomic(Metadata::new(), Atom::Literal(value)))
        }
        _ => None,
    }
}

fn swap_from_solution_to_current_ref(expr: &Expression) -> Option<Expression> {
    match expr {
        Expression::FromSolution(_, atom_expr) => Some(Expression::Atomic(
            Metadata::new(),
            atom_expr.as_ref().clone(),
        )),
        _ => None,
    }
}

fn add_represented_decision_values(solution: &mut HashMap<Name, Literal>, model: &ConjureModel) {
    let symbols = model.symbols().clone();
    let names = symbols.clone().into_iter().map(|x| x.0).collect::<Vec<_>>();
    let representations = names
        .into_iter()
        .filter_map(|name| {
            symbols
                .representations_for(&name)
                .map(|reprs| (name, reprs))
        })
        .filter_map(|(name, reprs)| {
            if reprs.is_empty() {
                return None;
            }
            if reprs.len() > 1 || reprs[0].len() != 1 {
                return None;
            }
            Some((name, reprs[0][0].clone()))
        })
        .collect::<Vec<_>>();

    if representations.is_empty() {
        return;
    }

    let mut solution_btree = solution
        .clone()
        .into_iter()
        .collect::<BTreeMap<Name, Literal>>();
    for (name, representation) in representations {
        let Ok(value) = representation.value_up(&solution_btree) else {
            continue;
        };
        solution.insert(name.clone(), value.clone());
        solution_btree.insert(name, value);
    }
}

fn simplify_expression_for_minion(expr: Expression) -> Expression {
    let mut current = expr;

    loop {
        let next = current.rewrite(&|e| {
            match &e {
                Expression::Not(_, inner) => match inner.as_ref() {
                    Expression::Atomic(_, Atom::Literal(Literal::Bool(value))) => {
                        return Some(Expression::Atomic(
                            Metadata::new(),
                            Atom::Literal(Literal::Bool(!value)),
                        ));
                    }
                    Expression::Not(_, inner_inner) => {
                        return Some(Moo::unwrap_or_clone(inner_inner.clone()));
                    }
                    Expression::And(_, terms) => {
                        if let Some((items, _)) = terms.as_ref().clone().unwrap_matrix_unchecked() {
                            let negated = items
                                .into_iter()
                                .map(|item| Expression::Not(Metadata::new(), Moo::new(item)))
                                .collect::<Vec<_>>();
                            return Some(Expression::Or(
                                Metadata::new(),
                                Moo::new(crate::into_matrix_expr![negated]),
                            ));
                        }
                    }
                    Expression::Or(_, terms) => {
                        if let Some((items, _)) = terms.as_ref().clone().unwrap_matrix_unchecked() {
                            let negated = items
                                .into_iter()
                                .map(|item| Expression::Not(Metadata::new(), Moo::new(item)))
                                .collect::<Vec<_>>();
                            return Some(Expression::And(
                                Metadata::new(),
                                Moo::new(crate::into_matrix_expr![negated]),
                            ));
                        }
                    }
                    _ => {}
                },
                Expression::And(_, terms) => {
                    if let Some((items, _)) = terms.as_ref().clone().unwrap_matrix_unchecked() {
                        if items.is_empty() {
                            return Some(Expression::Atomic(
                                Metadata::new(),
                                Atom::Literal(Literal::Bool(true)),
                            ));
                        }
                        if items.len() == 1 {
                            return Some(items[0].clone());
                        }
                    }
                }
                Expression::Or(_, terms) => {
                    if let Some((items, _)) = terms.as_ref().clone().unwrap_matrix_unchecked() {
                        if items.is_empty() {
                            return Some(Expression::Atomic(
                                Metadata::new(),
                                Atom::Literal(Literal::Bool(false)),
                            ));
                        }
                        if items.len() == 1 {
                            return Some(items[0].clone());
                        }
                    }
                }
                _ => {}
            }

            if let Some(lit) = eval_constant(&e) {
                return Some(Expression::Atomic(Metadata::new(), Atom::Literal(lit)));
            }

            run_partial_evaluator(&e)
                .ok()
                .map(|reduction| reduction.new_expression)
        });

        if next == current {
            return current;
        }

        current = next;
    }
}

impl Minion {
    pub fn new() -> Minion {
        Minion {
            __non_constructable: private::Internal,
            model: None,
            dominance_expression: None,
            dominance_model_template: None,
        }
    }

    fn add_dominance_constraints_for_solution(
        dominance_expression: Option<&Expression>,
        dominance_model_template: Option<&ConjureModel>,
        solution: &HashMap<Name, Literal>,
        minion_model: &mut MinionModel,
    ) -> Result<(), SolverError> {
        let Some(dominance_expression) = dominance_expression else {
            return Ok(());
        };

        let Some(model_template) = dominance_model_template else {
            return Ok(());
        };

        let rewritten_dominance = simplify_expression_for_minion(Expression::Not(
            Metadata::new(),
            Moo::new(
                dominance_expression
                    .rewrite(&|e| sub_in_solution_into_current_refs(&e, solution))
                    .rewrite(&|e| swap_from_solution_to_current_ref(&e)),
            ),
        ));
        eprintln!(
            "[minion dominance] rewritten blocker expression: {:?}",
            rewritten_dominance
        );

        let mut dominance_model = model_template.clone();
        dominance_model.replace_constraints(vec![]);
        dominance_model.replace_clauses(vec![]);
        dominance_model.dominance = None;
        dominance_model.add_constraint(rewritten_dominance);

        let rule_sets = dominance_model.context.read().unwrap().rule_sets.clone();
        let rewritten =
            rewrite_model_with_configured_rewriter(dominance_model, &rule_sets, current_rewriter())
                .map_err(|e| {
                    SolverError::Runtime(format!(
                        "Failed to rewrite dominance constraint for Minion solving: {e}"
                    ))
                })?;

        let mut dominance_minion_model = model_to_minion(rewritten)?;
        eprintln!(
            "[minion dominance] blocker minion model has {} vars and {} constraints",
            dominance_minion_model.named_variables.get_variable_order().len(),
            dominance_minion_model.constraints.len()
        );
        let existing_vars = minion_model
            .named_variables
            .get_variable_order()
            .into_iter()
            .collect::<HashSet<_>>();
        let dominance_search_vars = dominance_minion_model
            .named_variables
            .get_search_variable_order()
            .into_iter()
            .collect::<HashSet<_>>();

        for var_name in dominance_minion_model.named_variables.get_variable_order() {
            if existing_vars.contains(&var_name) {
                continue;
            }

            if dominance_search_vars.contains(&var_name) {
                return Err(SolverError::Runtime(format!(
                    "Dominance constraint introduced unexpected search variable {var_name:?} during Minion solving"
                )));
            }

            let domain = dominance_minion_model
                .named_variables
                .get_vartype(var_name.clone())
                .ok_or_else(|| {
                    SolverError::Runtime(format!(
                        "Missing Minion domain for dominance variable {var_name:?}"
                    ))
                })?;

            eprintln!(
                "[minion dominance] adding aux var {:?} with domain {:?}",
                var_name, domain
            );
            add_aux_var_during_search(var_name.clone(), domain.clone()).map_err(|e| {
                SolverError::Runtime(format!(
                    "Failed adding Minion dominance variable {var_name:?}: {e}"
                ))
            })?;

            minion_model
                .named_variables
                .add_aux_var(var_name.clone(), domain)
                .ok_or_else(|| {
                    SolverError::Runtime(format!(
                        "Failed tracking Minion dominance variable {var_name:?}"
                    ))
                })?;
        }

        for constraint in dominance_minion_model.constraints.drain(..) {
            eprintln!(
                "[minion dominance] adding constraint during search: {:?}",
                constraint
            );
            add_constraint_during_search(constraint.clone()).map_err(|e| {
                SolverError::Runtime(format!(
                    "Failed adding Minion dominance constraint during search: {e}"
                ))
            })?;
            minion_model.constraints.push(constraint);
        }

        Ok(())
    }
}

impl Default for Minion {
    fn default() -> Self {
        Minion::new()
    }
}

impl SolverAdaptor for Minion {
    #[allow(clippy::unwrap_used)]
    fn solve(
        &mut self,
        callback: SolverCallback,
        _: private::Internal,
    ) -> Result<SolveSuccess, SolverError> {
        // our minion callback is global state, so single threading the adaptor as a whole is
        // probably a good move...
        #[allow(clippy::unwrap_used)]
        let mut minion_lock = MINION_LOCK.lock().unwrap();

        let model = Arc::new(Mutex::new(self.model.clone().expect("STATE MACHINE ERR")));
        let hook_error: Arc<Mutex<Option<SolverError>>> = Arc::new(Mutex::new(None));
        let dominance_expression = self.dominance_expression.clone();
        let dominance_model_template = self.dominance_model_template.clone();

        #[allow(clippy::unwrap_used)]
        let mut user_callback = USER_CALLBACK
            .get_or_init(|| Mutex::new(Box::new(|x| true)))
            .lock()
            .unwrap();
        *user_callback = {
            let model = Arc::clone(&model);
            let hook_error = Arc::clone(&hook_error);
            Box::new(move |solution| {
                let solution_ix = SOLUTION_COUNTER.fetch_add(1, Ordering::SeqCst) + 1;
                eprintln!(
                    "[minion dominance] callback solution #{solution_ix}: {:?}",
                    solution
                );
                if !(callback)(solution.clone()) {
                    eprintln!(
                        "[minion dominance] user callback stopped after solution #{solution_ix}"
                    );
                    return false;
                }

                let mut dominance_solution = solution.clone();
                if let Some(model_template) = dominance_model_template.as_ref() {
                    add_represented_decision_values(&mut dominance_solution, model_template);
                }
                eprintln!(
                    "[minion dominance] enriched solution #{solution_ix}: {:?}",
                    dominance_solution
                );

                let mut model_guard = model.lock().unwrap();
                match Minion::add_dominance_constraints_for_solution(
                    dominance_expression.as_ref(),
                    dominance_model_template.as_ref(),
                    &dominance_solution,
                    &mut model_guard,
                ) {
                    Ok(()) => {
                        eprintln!(
                            "[minion dominance] blocker injected after solution #{solution_ix}"
                        );
                        true
                    }
                    Err(err) => {
                        eprintln!(
                            "[minion dominance] blocker injection failed after solution #{solution_ix}: {err}"
                        );
                        *hook_error.lock().unwrap() = Some(err);
                        false
                    }
                }
            })
        };
        drop(user_callback); // release mutex. REQUIRED so that run_minion can use the
        // user callback and not deadlock.

        USER_TERMINATED.store(false, Ordering::SeqCst);
        ANY_SOLUTIONS.store(false, Ordering::SeqCst);
        SOLUTION_COUNTER.store(0, Ordering::SeqCst);

        let initial_model = model.lock().unwrap().clone();
        run_minion(initial_model, minion_sys_callback).map_err(
            |err| match err {
                MinionError::RuntimeError(x) => Runtime(format!("{x:#?}")),
                MinionError::Other(x) => Runtime(format!("{x:#?}")),
                MinionError::NotImplemented(x) => RuntimeNotImplemented(x),
                x => Runtime(format!("unknown minion_sys error: {x:#?}")),
            },
        )?;

        self.model = Some(model.lock().unwrap().clone());
        if let Some(err) = hook_error.lock().unwrap().take() {
            return Err(err);
        }

        let status = if USER_TERMINATED.load(Ordering::SeqCst) {
            Incomplete(UserTerminated)
        } else if ANY_SOLUTIONS.load(Ordering::SeqCst) {
            Complete(HasSolutions)
        } else {
            Complete(NoSolutions)
        };
        Ok(SolveSuccess {
            stats: get_solver_stats(),
            status,
        })
    }

    fn solve_mut(
        &mut self,
        callback: SolverMutCallback,
        _: private::Internal,
    ) -> Result<SolveSuccess, SolverError> {
        Err(OpNotImplemented("solve_mut".into()))
    }

    fn load_model(&mut self, model: ConjureModel, _: private::Internal) -> Result<(), SolverError> {
        self.dominance_expression = model.dominance.as_ref().map(|expr| match expr {
            Expression::DominanceRelation(_, inner) => inner.as_ref().clone(),
            _ => expr.clone(),
        });
        self.dominance_model_template = self.dominance_expression.as_ref().map(|_| model.clone());
        self.model = Some(model_to_minion(model)?);
        Ok(())
    }

    fn get_family(&self) -> SolverFamily {
        SolverFamily::Minion
    }

    fn get_name(&self) -> &'static str {
        "minion"
    }

    fn write_solver_input_file(
        &self,
        writer: &mut Box<dyn std::io::Write>,
    ) -> Result<(), std::io::Error> {
        let model = self.model.as_ref().expect("Minion solver adaptor should have a model as write_solver_input_file should only be called in the LoadedModel state.");
        minion_sys::print::write_minion_file(writer, model)
    }
}

#[allow(clippy::unwrap_used)]
fn get_solver_stats() -> SolverStats {
    SolverStats {
        nodes: get_from_table("Nodes".into()).map(|x| x.parse::<u64>().unwrap()),
        ..Default::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{DeclarationPtr, Domain, Reference};
    use crate::context::Context;
    use crate::settings::{Rewriter, set_current_rewriter};

    #[test]
    fn minion_dominance_programming_keeps_only_non_dominated_solution() {
        let context = Context::new_ptr_empty(SolverFamily::Minion);
        set_current_rewriter(Rewriter::Naive);

        let x = Name::User("x".into());
        let y = Name::User("y".into());

        let x_decl = DeclarationPtr::new_find(x.clone(), Domain::bool());
        let y_decl = DeclarationPtr::new_find(y.clone(), Domain::bool());
        let x_ref = Expression::Atomic(
            Metadata::new(),
            Atom::Reference(Reference::new(x_decl.clone())),
        );
        let y_ref = Expression::Atomic(
            Metadata::new(),
            Atom::Reference(Reference::new(y_decl.clone())),
        );

        let mut model = ConjureModel::new(context);
        model.add_symbol(x_decl);
        model.add_symbol(y_decl);
        model.dominance =
            Some(Expression::DominanceRelation(
                Metadata::new(),
                Moo::new(Expression::And(
                    Metadata::new(),
                    Moo::new(crate::matrix_expr![
                        Expression::Imply(
                            Metadata::new(),
                            Moo::new(x_ref.clone()),
                            Moo::new(Expression::FromSolution(
                                Metadata::new(),
                                Moo::new(Atom::Reference(Reference::new(
                                    DeclarationPtr::new_find(x.clone(), Domain::bool(),)
                                ))),
                            )),
                        ),
                        Expression::Imply(
                            Metadata::new(),
                            Moo::new(y_ref.clone()),
                            Moo::new(Expression::FromSolution(
                                Metadata::new(),
                                Moo::new(Atom::Reference(Reference::new(
                                    DeclarationPtr::new_find(y.clone(), Domain::bool(),)
                                ))),
                            )),
                        ),
                        Expression::Or(
                            Metadata::new(),
                            Moo::new(crate::matrix_expr![
                                Expression::And(
                                    Metadata::new(),
                                    Moo::new(crate::matrix_expr![
                                        Expression::Not(Metadata::new(), Moo::new(x_ref.clone())),
                                        Expression::FromSolution(
                                            Metadata::new(),
                                            Moo::new(Atom::Reference(Reference::new(
                                                DeclarationPtr::new_find(x.clone(), Domain::bool()),
                                            ))),
                                        ),
                                    ]),
                                ),
                                Expression::And(
                                    Metadata::new(),
                                    Moo::new(crate::matrix_expr![
                                        Expression::Not(Metadata::new(), Moo::new(y_ref.clone())),
                                        Expression::FromSolution(
                                            Metadata::new(),
                                            Moo::new(Atom::Reference(Reference::new(
                                                DeclarationPtr::new_find(y.clone(), Domain::bool()),
                                            ))),
                                        ),
                                    ]),
                                ),
                            ]),
                        ),
                    ]),
                )),
            ));

        let mut minion = Minion::new();
        minion
            .load_model(model, private::Internal)
            .expect("Minion model should load");

        let solutions = Arc::new(Mutex::new(Vec::<HashMap<Name, Literal>>::new()));
        let solutions_for_callback = Arc::clone(&solutions);
        minion
            .solve(
                Box::new(move |solution| {
                    solutions_for_callback.lock().unwrap().push(solution);
                    true
                }),
                private::Internal,
            )
            .expect("Minion solve should succeed");

        let solutions = solutions.lock().unwrap();
        assert_eq!(solutions.len(), 1);
        let solution = &solutions[0];
        assert_eq!(solution.get(&x), Some(&Literal::Int(0)));
        assert_eq!(solution.get(&y), Some(&Literal::Int(0)));
    }
}
