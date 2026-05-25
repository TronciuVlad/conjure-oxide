#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
OUT_CSV="${OUT_CSV:-$SCRIPT_DIR/gcm-cdp-minion-timings.csv}"
OUT_TXT="${OUT_TXT:-$SCRIPT_DIR/gcm-cdp-minion-timings-comparison.txt}"
TIMEOUT_SECS="${TIMEOUT_SECS:-360}"
N_SOLUTIONS="${N_SOLUTIONS:-1}"

# Prefer an explicit binary path if provided, otherwise use conjure-oxide-debug on PATH.
COX_BIN="${COX_BIN:-conjure-oxide-debug}"

# If a custom Z3 location is provided, also expose it to the runtime loader.
# This avoids "error while loading shared libraries: libz3.so" for binaries/build scripts.
if [[ -n "${Z3_LIBRARY_PATH_OVERRIDE:-}" ]]; then
  export LD_LIBRARY_PATH="${Z3_LIBRARY_PATH_OVERRIDE}:${LD_LIBRARY_PATH:-}"
fi

# Solver args chosen to exercise CDP with Minion.
COMMON_ARGS=(
  solve
  --parser tree-sitter
  --rewriter morph-levelson-fixedpoint
  --solver minion
  -n "$N_SOLUTIONS"
)

MODELS=(
  "RC.eprime"
  "SRC-asymmetric.eprime"
  "SRC-spo.eprime"
  "SRC-acyclic.eprime"
  "SRC-multivariate.eprime"
)

PARAMS=(
  "params/100166617566-RC.eprime-param"
  "params/100166617566-SRC-asymmetric.eprime-param"
  "params/100166617566-SRC-spo.eprime-param"
  "params/100166617566-SRC-acyclic.eprime-param"
  "params/100166617566-SRC-multivariate.eprime-param"
)

if ! command -v "$COX_BIN" >/dev/null 2>&1; then
  echo "error: could not find executable '$COX_BIN'" >&2
  echo "hint: set COX_BIN=/path/to/conjure-oxide-debug" >&2
  exit 1
fi

if ! command -v timeout >/dev/null 2>&1; then
  echo "error: required command 'timeout' was not found" >&2
  exit 1
fi

run_one() {
  local mode="$1"
  local model_rel="$2"
  local param_rel="$3"

  local model_path="$SCRIPT_DIR/$model_rel"
  local param_path="$SCRIPT_DIR/$param_rel"

  local start_ns
  local end_ns
  local stderr_log
  stderr_log=$(mktemp "${TMPDIR:-/tmp}/gcm-cdp-minion-stderr.XXXXXX")
  trap 'rm -f "$stderr_log"' RETURN
  start_ns=$(date +%s%N)

  local -a run_cmd
  run_cmd=("$COX_BIN" "${COMMON_ARGS[@]}" "$model_path" "$param_path")

  set +e
  if [[ "$mode" == "injection_off" ]]; then
    if [[ "$TIMEOUT_SECS" == "none" || "$TIMEOUT_SECS" == "0" ]]; then
      CONJURE_MINION_DISABLE_CDP_INJECTION=1 "${run_cmd[@]}" >/dev/null 2>"$stderr_log"
    else
      CONJURE_MINION_DISABLE_CDP_INJECTION=1 \
        timeout "$TIMEOUT_SECS" "${run_cmd[@]}" >/dev/null 2>"$stderr_log"
    fi
  else
    if [[ "$TIMEOUT_SECS" == "none" || "$TIMEOUT_SECS" == "0" ]]; then
      "${run_cmd[@]}" >/dev/null 2>"$stderr_log"
    else
      timeout "$TIMEOUT_SECS" "${run_cmd[@]}" >/dev/null 2>"$stderr_log"
    fi
  fi
  local rc=$?
  set -e

  end_ns=$(date +%s%N)

  local elapsed_s
  elapsed_s=$(awk -v s="$start_ns" -v e="$end_ns" 'BEGIN { printf "%.2f", (e-s)/1000000000.0 }')

  local status="ok"
  local retained="n/a"
  local total="n/a"
  local retained_summary="n/a"
  if [[ $rc -eq 124 ]]; then
    status="timeout"
  elif [[ $rc -ne 0 ]]; then
    status="error"
  fi

  # Canonical stderr format:
  # "Dominance pruning retained X of Y solutions."
  local prune_line
  prune_line=$(grep -F "Dominance pruning retained" "$stderr_log" | tail -n 1 || true)
  if [[ -n "$prune_line" ]]; then
    retained=$(echo "$prune_line" | awk '{print $4}')
    total=$(echo "$prune_line" | awk '{print $6}')
    retained_summary="retained ${retained} solutions out of ${total}"
  fi

  printf "%s,%s,%s,%d,%s,%s,%s,%s\n" \
    "$mode" "$model_rel" "$elapsed_s" "$rc" "$status" "$retained" "$total" "$retained_summary" >> "$OUT_CSV"
  printf "[%s] %-24s %8ss (rc=%d, %s; %s)\n" \
    "$mode" "$model_rel" "$elapsed_s" "$rc" "$status" "$retained_summary" >&2
}

build_comparison() {
  {
    echo "GCM CDP Minion Timing Comparison"
    echo "Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
    echo "Per-case timeout: ${TIMEOUT_SECS}s"
    echo
    printf "%-22s %-20s %-20s %-16s %-36s %-36s\n" \
      "Model" "off(s,status)" "on(s,status)" "delta off-on" "off retention" "on retention"
    printf "%-22s %-20s %-20s %-16s %-36s %-36s\n" \
      "-----" "-------------" "------------" "------------" "-------------" "------------"

    for i in "${!MODELS[@]}"; do
      local model="${MODELS[$i]}"
      local off_line on_line
      off_line=$(grep "^injection_off,${model}," "$OUT_CSV" || true)
      on_line=$(grep "^injection_on,${model}," "$OUT_CSV" || true)

      local off_s off_status on_s on_status off_ret off_total on_ret on_total delta
      off_s=$(echo "$off_line" | cut -d, -f3)
      off_status=$(echo "$off_line" | cut -d, -f5)
      off_ret=$(echo "$off_line" | cut -d, -f6)
      off_total=$(echo "$off_line" | cut -d, -f7)
      on_s=$(echo "$on_line" | cut -d, -f3)
      on_status=$(echo "$on_line" | cut -d, -f5)
      on_ret=$(echo "$on_line" | cut -d, -f6)
      on_total=$(echo "$on_line" | cut -d, -f7)

      if [[ -n "$off_s" && -n "$on_s" ]]; then
        delta=$(awk -v off="$off_s" -v on="$on_s" 'BEGIN { printf "%.3f", off - on }')
      else
        delta="n/a"
      fi

      printf "%-22s %-20s %-20s %-16s %-36s %-36s\n" \
        "$model" \
        "${off_s:-n/a},${off_status:-n/a}" \
        "${on_s:-n/a},${on_status:-n/a}" \
        "$delta" \
        "retained ${off_ret:-n/a} solutions out of ${off_total:-n/a}" \
        "retained ${on_ret:-n/a} solutions out of ${on_total:-n/a}"
    done
  } > "$OUT_TXT"
}

echo "mode,model,seconds,exit_code,status,retained_solutions,total_solutions,retention_summary" > "$OUT_CSV"

for i in "${!MODELS[@]}"; do
  run_one "injection_off" "${MODELS[$i]}" "${PARAMS[$i]}"
done

for i in "${!MODELS[@]}"; do
  run_one "injection_on" "${MODELS[$i]}" "${PARAMS[$i]}"
done

build_comparison

echo "wrote: $OUT_CSV"
echo "wrote: $OUT_TXT"
