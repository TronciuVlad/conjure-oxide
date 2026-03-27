#![allow(clippy::panic_in_result_fn, clippy::unwrap_used)]

use std::collections::{BTreeSet, HashMap};
use std::sync::{Mutex, MutexGuard, OnceLock};

use minion_sys::ast::{Constant, Constraint, Model, Var, VarDomain, VarName};
use minion_sys::{add_aux_var_during_search, add_constraint_during_search, run_minion};

static TEST_LOCK: Mutex<()> = Mutex::new(());
static SCENARIO_STATE: OnceLock<Mutex<Option<ScenarioState>>> = OnceLock::new();

#[derive(Clone, Copy, Debug)]
enum ScenarioKind {
    InjectFalseAfterFirstSolution,
    AddAuxVarOnlyAfterFirstSolution,
    AddAuxVarAndBindXAfterFirstSolution,
    TightenWeightedSumAfterFirstSolution,
    AddComplementWatchedOrOnEachSolution,
    AddNestedComplementClauseOnEachSolution,
    AddSubsetParetoShapeClauseOnEachSolution,
}

#[derive(Debug)]
struct ScenarioState {
    kind: ScenarioKind,
    callback_count: usize,
    solutions: Vec<HashMap<VarName, Constant>>,
    callback_error: Option<String>,
}

#[derive(Debug)]
struct ScenarioOutcome {
    state: ScenarioState,
    run_error: Option<String>,
}

impl ScenarioState {
    fn new(kind: ScenarioKind) -> Self {
        Self {
            kind,
            callback_count: 0,
            solutions: Vec::new(),
            callback_error: None,
        }
    }
}

fn scenario_state() -> &'static Mutex<Option<ScenarioState>> {
    SCENARIO_STATE.get_or_init(|| Mutex::new(None))
}

fn lock_unpoisoned<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    match mutex.lock() {
        Ok(guard) => guard,
        Err(poisoned) => poisoned.into_inner(),
    }
}

fn callback(solution: HashMap<VarName, Constant>) -> bool {
    let (kind, callback_count) = {
        let mut guard = lock_unpoisoned(scenario_state());
        let state = guard
            .as_mut()
            .expect("mid-search test callback ran without configured state");
        state.callback_count += 1;
        state.solutions.push(solution.clone());
        (state.kind, state.callback_count)
    };

    let result: Result<(), minion_sys::error::MinionError> = match kind {
        ScenarioKind::InjectFalseAfterFirstSolution => {
            if callback_count == 1 {
                add_constraint_during_search(Constraint::False)
            } else {
                Ok(())
            }
        }
        ScenarioKind::AddAuxVarOnlyAfterFirstSolution => {
            if callback_count == 1 {
                add_aux_var_during_search("x_snapshot".to_owned(), VarDomain::Bool)
            } else {
                Ok(())
            }
        }
        ScenarioKind::AddAuxVarAndBindXAfterFirstSolution => {
            if callback_count == 1 {
                let x = value(&solution, "x");
                add_aux_var_during_search("x_snapshot".to_owned(), VarDomain::Bool)
                    .and_then(|()| {
                        add_constraint_during_search(Constraint::WLiteral(
                            Var::NameRef("x_snapshot".to_owned()),
                            Constant::Integer(x),
                        ))
                    })
                    .and_then(|()| {
                        add_constraint_during_search(Constraint::Eq(
                            Var::NameRef("x".to_owned()),
                            Var::NameRef("x_snapshot".to_owned()),
                        ))
                    })
            } else {
                Ok(())
            }
        }
        ScenarioKind::TightenWeightedSumAfterFirstSolution => {
            if callback_count == 1 {
                let y = value(&solution, "y");
                let z = value(&solution, "z");
                add_constraint_during_search(Constraint::WeightedSumLeq(
                    vec![Constant::Integer(1), Constant::Integer(1)],
                    vec![Var::NameRef("y".to_owned()), Var::NameRef("z".to_owned())],
                    Var::ConstantAsVar(y + z),
                ))
            } else {
                Ok(())
            }
        }
        ScenarioKind::AddComplementWatchedOrOnEachSolution => {
            add_constraint_during_search(complement_watched_or(&solution, &["a", "b", "c"]))
        }
        ScenarioKind::AddNestedComplementClauseOnEachSolution => {
            add_constraint_during_search(nested_complement_watched_or(&solution, &["a", "b", "c"]))
        }
        ScenarioKind::AddSubsetParetoShapeClauseOnEachSolution => add_constraint_during_search(
            subset_pareto_shape_clause(&solution, &["a", "b", "c", "d", "e"]),
        ),
    };

    if let Err(err) = result {
        lock_unpoisoned(scenario_state())
            .as_mut()
            .unwrap()
            .callback_error = Some(err.to_string());
        return false;
    }

    true
}

fn run_scenario(model: Model, kind: ScenarioKind) -> ScenarioOutcome {
    let _test_guard = lock_unpoisoned(&TEST_LOCK);

    {
        let mut guard = lock_unpoisoned(scenario_state());
        *guard = Some(ScenarioState::new(kind));
    }

    let run_result = run_minion(model, callback);
    let state = lock_unpoisoned(scenario_state())
        .take()
        .expect("mid-search scenario state should exist after run");

    ScenarioOutcome {
        state,
        run_error: run_result.err().map(|err| err.to_string()),
    }
}

fn bool_grid_model(names: &[&str]) -> Model {
    let mut model = Model::new();
    for name in names {
        model
            .named_variables
            .add_var((*name).to_owned(), VarDomain::Bool);
    }
    model
}

fn bool_grid_model_with_exactly_k_ones(names: &[&str], k: i32) -> Model {
    let mut model = bool_grid_model(names);
    let vars = names
        .iter()
        .map(|name| Var::NameRef((*name).to_owned()))
        .collect::<Vec<_>>();
    model
        .constraints
        .push(Constraint::WatchSumGeq(vars.clone(), Constant::Integer(k)));
    model
        .constraints
        .push(Constraint::WatchSumLeq(vars, Constant::Integer(k)));
    model
}

fn weighted_sum_probe_model() -> Model {
    let mut model = Model::new();
    model
        .named_variables
        .add_var("x".to_owned(), VarDomain::Bool);
    model
        .named_variables
        .add_var("y".to_owned(), VarDomain::Bool);
    model
        .named_variables
        .add_var("z".to_owned(), VarDomain::Bool);

    model.constraints.push(Constraint::WLiteral(
        Var::NameRef("x".to_owned()),
        Constant::Integer(0),
    ));

    model
}

fn value(solution: &HashMap<VarName, Constant>, name: &str) -> i32 {
    match solution.get(name) {
        Some(Constant::Integer(n)) => *n,
        Some(Constant::Bool(true)) => 1,
        Some(Constant::Bool(false)) => 0,
        Some(_) => panic!("solution contained an unsupported constant type for {name}"),
        None => panic!("solution did not contain variable {name}"),
    }
}

fn complement_watched_or(solution: &HashMap<VarName, Constant>, names: &[&str]) -> Constraint {
    Constraint::WatchedOr(
        names
            .iter()
            .map(|name| {
                Constraint::WLiteral(
                    Var::NameRef((*name).to_owned()),
                    Constant::Integer(value(solution, name)),
                )
            })
            .collect(),
    )
}

fn nested_complement_watched_or(
    solution: &HashMap<VarName, Constant>,
    names: &[&str],
) -> Constraint {
    Constraint::WatchedOr(
        names
            .iter()
            .map(|name| {
                Constraint::WatchedAnd(vec![Constraint::WLiteral(
                    Var::NameRef((*name).to_owned()),
                    Constant::Integer(value(solution, name)),
                )])
            })
            .collect(),
    )
}

fn subset_pareto_shape_clause(
    solution: &HashMap<VarName, Constant>,
    names: &[&str],
) -> Constraint {
    let zeros = names
        .iter()
        .copied()
        .filter(|name| value(solution, name) == 0)
        .collect::<Vec<_>>();
    let ones = names
        .iter()
        .copied()
        .filter(|name| value(solution, name) == 1)
        .collect::<Vec<_>>();

    let zero_literals = zeros
        .iter()
        .map(|name| {
            Constraint::WLiteral(
                Var::NameRef((*name).to_owned()),
                Constant::Integer(0),
            )
        })
        .collect::<Vec<_>>();
    let one_literals = ones
        .iter()
        .map(|name| {
            Constraint::WLiteral(
                Var::NameRef((*name).to_owned()),
                Constant::Integer(0),
            )
        })
        .collect::<Vec<_>>();

    let zero_clause = match zero_literals.as_slice() {
        [] => Constraint::True,
        [single] => single.clone(),
        [left, right] => Constraint::WatchedAnd(vec![left.clone(), right.clone()]),
        [first, second, third] => Constraint::WatchedAnd(vec![
            Constraint::WatchedAnd(vec![first.clone(), second.clone()]),
            third.clone(),
        ]),
        [first, second, rest @ ..] => Constraint::WatchedAnd(vec![
            Constraint::WatchedAnd(vec![first.clone(), second.clone()]),
            Constraint::WatchedAnd(rest.to_vec()),
        ]),
    };

    let one_clause = match one_literals.as_slice() {
        [] => Constraint::False,
        [single] => single.clone(),
        _ => Constraint::WatchedOr(one_literals),
    };

    Constraint::WatchedOr(vec![one_clause, zero_clause])
}

fn solution_key(solution: &HashMap<VarName, Constant>, names: &[&str]) -> Vec<i32> {
    names.iter().map(|name| value(solution, name)).collect()
}

fn complement_key(key: &[i32]) -> Vec<i32> {
    key.iter().map(|bit| 1 - bit).collect()
}

#[test]
fn add_mid_search_operations_require_active_callback() {
    let err = add_aux_var_during_search("outside".to_owned(), VarDomain::Bool)
        .expect_err("adding a variable outside a callback should fail");
    assert!(err.to_string().contains("outside an active callback"));

    let err = add_constraint_during_search(Constraint::True)
        .expect_err("adding a constraint outside a callback should fail");
    assert!(err.to_string().contains("outside an active callback"));
}

#[test]
fn mid_search_false_constraint_stops_after_first_solution() {
    let outcome = run_scenario(
        bool_grid_model(&["x", "y"]),
        ScenarioKind::InjectFalseAfterFirstSolution,
    );

    assert_eq!(outcome.state.solutions.len(), 1);
    assert_eq!(outcome.run_error, None);
    assert!(
        outcome
            .state
            .callback_error
            .as_ref()
            .is_some_and(|err| err.contains("immediate failure"))
    );
}

#[test]
fn mid_search_aux_var_insertion_is_stable() {
    let outcome = run_scenario(
        bool_grid_model(&["x", "y"]),
        ScenarioKind::AddAuxVarOnlyAfterFirstSolution,
    );

    assert_eq!(outcome.state.callback_error, None);
    assert_eq!(outcome.run_error, None);
    assert_eq!(outcome.state.solutions.len(), 4);
}

#[test]
fn mid_search_aux_var_can_bind_existing_search_variable() {
    let outcome = run_scenario(
        bool_grid_model(&["x", "y"]),
        ScenarioKind::AddAuxVarAndBindXAfterFirstSolution,
    );

    let first_x = value(&outcome.state.solutions[0], "x");
    assert_eq!(outcome.run_error, None);
    assert_eq!(outcome.state.callback_error, None);
    assert_eq!(outcome.state.solutions.len(), 2);
    assert!(
        outcome
            .state
            .solutions
            .iter()
            .all(|solution| value(solution, "x") == first_x)
    );
}

#[test]
fn mid_search_weighted_sum_can_tighten_integer_space() {
    let outcome = run_scenario(
        weighted_sum_probe_model(),
        ScenarioKind::TightenWeightedSumAfterFirstSolution,
    );

    assert_eq!(outcome.state.callback_error, None);
    assert_eq!(outcome.run_error, None);
    assert_eq!(outcome.state.solutions.len(), 1);
    assert_eq!(value(&outcome.state.solutions[0], "x"), 0);
    assert_eq!(
        value(&outcome.state.solutions[0], "y") + value(&outcome.state.solutions[0], "z"),
        0
    );
}

#[test]
#[ignore = "manual reproducer for watched-or mid-search pruning semantics"]
fn mid_search_watched_or_complement_clauses_remain_stable() {
    let outcome = run_scenario(
        bool_grid_model(&["a", "b", "c"]),
        ScenarioKind::AddComplementWatchedOrOnEachSolution,
    );

    let names = ["a", "b", "c"];
    let keys = outcome
        .state
        .solutions
        .iter()
        .map(|solution| solution_key(solution, &names))
        .collect::<BTreeSet<_>>();

    assert_eq!(outcome.run_error, None);
    assert_eq!(outcome.state.callback_error, None);
    assert_eq!(keys.len(), outcome.state.solutions.len());
    assert_eq!(keys.len(), 4);
    for key in &keys {
        assert!(!keys.contains(&complement_key(key)));
    }
}

#[test]
#[ignore = "manual reproducer for nested watched-and/or mid-search behaviour"]
fn mid_search_nested_parent_clauses_remain_stable() {
    let outcome = run_scenario(
        bool_grid_model(&["a", "b", "c"]),
        ScenarioKind::AddNestedComplementClauseOnEachSolution,
    );

    let names = ["a", "b", "c"];
    let keys = outcome
        .state
        .solutions
        .iter()
        .map(|solution| solution_key(solution, &names))
        .collect::<BTreeSet<_>>();

    assert_eq!(outcome.run_error, None);
    assert_eq!(outcome.state.callback_error, None);
    assert_eq!(keys.len(), outcome.state.solutions.len());
    assert_eq!(keys.len(), 4);
    for key in &keys {
        assert!(!keys.contains(&complement_key(key)));
    }
}

#[test]
#[ignore = "manual reproducer for subset-pareto blocker shape mid-search behaviour"]
fn mid_search_subset_pareto_shape_clause_remains_stable() {
    let outcome = run_scenario(
        bool_grid_model_with_exactly_k_ones(&["a", "b", "c", "d", "e"], 2),
        ScenarioKind::AddSubsetParetoShapeClauseOnEachSolution,
    );

    assert_eq!(outcome.run_error, None);
    assert_eq!(outcome.state.callback_error, None);
}
