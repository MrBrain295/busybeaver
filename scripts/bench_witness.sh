#!/usr/bin/env bash
#
# Witness-store regression guard for `beaver`.
#
# Checks three things on a from-scratch BB(4,2) run:
#   1. Correctness — the --trusted re-run reports the SAME value as generation.
#   2. Generation is fast        (< GEN_LIMIT_MS, default 30000 — a 12-core-dev target).
#   3. --trusted is ~instant     (< TRUSTED_LIMIT_MS, default 1000 — hardware-independent,
#                                 it is a single cached-row read).
#
# Exits non-zero (printing FAIL) on any violation, so it can run in CI.
# Tune via env: GEN_LIMIT_MS, TRUSTED_LIMIT_MS, ARGS (e.g. ARGS="3 2").
# CI runs on slower hardware than a dev box, so set a generous GEN_LIMIT_MS there;
# correctness and the trusted bound stay meaningful regardless of core count.
set -euo pipefail

GEN_LIMIT_MS=${GEN_LIMIT_MS:-30000}
TRUSTED_LIMIT_MS=${TRUSTED_LIMIT_MS:-1000}
ARGS=${ARGS:-"4 2"}

DB="$(mktemp -u).db"
cleanup() { rm -f "$DB" "$DB-wal" "$DB-shm"; }
trap cleanup EXIT

echo "Building beaver…"
lake build beaver >/dev/null

ms()  { grep -oE 'In: [0-9]+ms' | grep -oE '[0-9]+'; }
val() { awk '/Busybeaver\(/ {v=$NF} END {print v}'; }   # last token of the result line

echo "Generating witness (beaver $ARGS)…"
# shellcheck disable=SC2086
gen_out=$(lake exe beaver $ARGS --witness "$DB" 2>/dev/null)
echo "Trusted re-run (beaver $ARGS --trusted)…"
# shellcheck disable=SC2086
trusted_out=$(lake exe beaver $ARGS --trusted --witness "$DB" 2>/dev/null)
echo "Verified re-run (beaver $ARGS --verify)…"
# shellcheck disable=SC2086
verify_out=$(lake exe beaver $ARGS --verify 2>/dev/null)

# `|| true`: a missing `In:` line must not abort the script under `set -e`; the
# emptiness checks below fail loudly instead. (`val` via awk is empty-safe already.)
gen_ms=$(printf '%s\n' "$gen_out" | ms || true)
trusted_ms=$(printf '%s\n' "$trusted_out" | ms || true)
gen_val=$(printf '%s\n' "$gen_out" | val)
trusted_val=$(printf '%s\n' "$trusted_out" | val)
verify_val=$(printf '%s\n' "$verify_out" | val)

echo
echo "value:    generate=$gen_val  trusted=$trusted_val  verify=$verify_val"
echo "generate: ${gen_ms}ms   (limit ${GEN_LIMIT_MS}ms)"
echo "trusted:  ${trusted_ms}ms   (limit ${TRUSTED_LIMIT_MS}ms)"

fail=0

# Parsing sanity — a missing timing means the run errored or the output changed.
if [ -z "$gen_ms" ] || [ -z "$trusted_ms" ]; then
  echo "FAIL: could not parse 'In: <n>ms' timing from beaver output"; fail=1
fi

# The run must FULLY decide the size. An undecided/lower-bound result prints
# `#Undec:` / `Busybeaver(...) >= N`; the value checks alone would still pass
# (--trusted replays the same incomplete aggregate), so reject it explicitly.
if printf '%s\n' "$gen_out" | grep -qE '#Undec|≥'; then
  echo "FAIL: generation did not fully decide (undecided / lower-bound result):"
  printf '%s\n' "$gen_out" | grep -E 'Busybeaver|#Undec'
  fail=1
fi

# Value agreement: generate == trusted == verified. The verify check is what
# guards that the (unverified) witness walk still agrees with the certified compute.
if [ -z "$gen_val" ] || [ "$gen_val" != "$trusted_val" ]; then
  echo "FAIL: trusted value ($trusted_val) does not match generated value ($gen_val)"; fail=1
fi
if [ -z "$verify_val" ] || [ "$gen_val" != "$verify_val" ]; then
  echo "FAIL: verified value ($verify_val) does not match generated value ($gen_val) — witness walk diverged from the certified compute"; fail=1
fi

# Time bounds (only when the timing parsed).
if [ -n "$gen_ms" ] && [ "$gen_ms" -ge "$GEN_LIMIT_MS" ]; then echo "FAIL: generation exceeded ${GEN_LIMIT_MS}ms"; fail=1; fi
if [ -n "$trusted_ms" ] && [ "$trusted_ms" -ge "$TRUSTED_LIMIT_MS" ]; then echo "FAIL: trusted exceeded ${TRUSTED_LIMIT_MS}ms"; fail=1; fi

[ "$fail" -eq 0 ] && echo "PASS"
exit "$fail"
