#!/usr/bin/env bash
# Run the full LeanBzip2 test matrix: Lean suites + CLI/system-bzip2 smoke tests.
# Opt-in large/stress suite: LEANBZIP2_RUN_LARGE=1 ./scripts/run_tests.sh
set -u
cd "$(dirname "$0")/.."

failures=0

run_suite() {
  echo "=== $1 ==="
  if ! lake env lean --run "$1"; then
    echo "SUITE FAILED: $1"
    failures=$((failures + 1))
  fi
  echo
}

run_suite tests/test_bzip2_format.lean
run_suite tests/test_bz2_exact.lean
run_suite tests/test_bzip2_shell.lean

if [ "${LEANBZIP2_RUN_LARGE:-0}" = "1" ]; then
  run_suite tests/test_bzip2_large.lean
fi

echo "=== CLI smoke tests ==="
if ! lake build bzip2 >/dev/null; then
  echo "SUITE FAILED: lake build bzip2"
  failures=$((failures + 1))
else
  BIN="$PWD/.lake/build/bin/bzip2"
  T="$(mktemp -d)"
  smoke_fail=0
  check() {
    if [ "$2" != "$3" ]; then
      echo "FAIL: $1 (exit $2, want $3)"
      smoke_fail=1
    fi
  }

  head -c 100000 /dev/urandom > "$T/rand.bin"
  printf 'leanbzip2 smoke test\n%.0s' {1..2000} > "$T/text.txt"
  : > "$T/empty.bin"

  for f in rand.bin text.txt empty.bin; do
    "$BIN" -kc "$T/$f" > "$T/$f.bz2"
    if command -v bzip2 >/dev/null; then
      bzip2 -t "$T/$f.bz2" || { echo "FAIL: bzip2 -t $f"; smoke_fail=1; }
      bzip2 -dc "$T/$f.bz2" | cmp -s - "$T/$f" || { echo "FAIL: cross-decode $f"; smoke_fail=1; }
      bzip2 -kc "$T/$f" > "$T/$f.sys.bz2"
      "$BIN" -dc "$T/$f.sys.bz2" | cmp -s - "$T/$f" || { echo "FAIL: ours-decode $f"; smoke_fail=1; }
    fi
    "$BIN" -dc "$T/$f.bz2" | cmp -s - "$T/$f" || { echo "FAIL: self-roundtrip $f"; smoke_fail=1; }
  done

  echo smoke | "$BIN" | "$BIN" -d | grep -q smoke || { echo "FAIL: pipe roundtrip"; smoke_fail=1; }
  "$BIN" -t "$T/rand.bin.bz2"; check "test-good" $? 0
  head -c 40 "$T/rand.bin.bz2" > "$T/trunc.bz2"
  "$BIN" -qt "$T/trunc.bz2"; check "test-corrupt" $? 2
  "$BIN" -qt "$T/nonexistent.bz2"; check "missing-input" $? 1

  rm -rf "$T"
  if [ "$smoke_fail" != "0" ]; then
    echo "SUITE FAILED: CLI smoke tests"
    failures=$((failures + 1))
  else
    echo "CLI smoke tests passed"
  fi
fi

echo
if [ "$failures" != "0" ]; then
  echo "RESULT: $failures suite(s) failed"
  exit 1
fi
echo "RESULT: all suites passed"
