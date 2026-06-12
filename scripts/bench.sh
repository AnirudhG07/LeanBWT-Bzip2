#!/usr/bin/env bash
# Benchmark LeanBzip2 against system bzip2: wall time and compressed size.
# Usage: ./scripts/bench.sh [block-size-digit]   (default 9)
set -eu
cd "$(dirname "$0")/.."

DIGIT="${1:-9}"
lake build bzip2 >/dev/null
BIN="$PWD/.lake/build/bin/bzip2"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT

# Corpora
cat ./Bzip2/**/*.lean ./Bzip2/*.lean ./tests/*.lean > "$T/source.txt" 2>/dev/null || \
  find . -name '*.lean' -not -path './.lake/*' -exec cat {} + > "$T/source.txt"
head -c 2000000 /dev/urandom > "$T/random.bin"
yes 'all work and no play makes bzip2 a dull tool' | head -c 5000000 > "$T/repetitive.txt"
if [ -r /usr/share/dict/words ]; then
  cp /usr/share/dict/words "$T/words.txt"
fi

now_ms() { date +%s%3N; }

bench_one() {
  local tool_name="$1" cmd="$2" input="$3" output="$4"
  local start end
  start=$(now_ms)
  $cmd -"$DIGIT" -kc "$input" > "$output"
  end=$(now_ms)
  local size
  size=$(stat -c %s "$output")
  echo "$tool_name $((end - start)) $size"
}

printf '%-16s %12s %14s %14s %14s %14s %8s\n' \
  corpus bytes "lean ms" "lean out" "bzip2 ms" "bzip2 out" "ratio%"
for f in "$T"/*; do
  name="$(basename "$f")"
  case "$name" in *.bz2) continue;; esac
  insize=$(stat -c %s "$f")

  read -r _ lean_ms lean_out <<< "$(bench_one lean "$BIN" "$f" "$f.lean.bz2")"
  if command -v bzip2 >/dev/null; then
    read -r _ sys_ms sys_out <<< "$(bench_one bzip2 bzip2 "$f" "$f.sys.bz2")"
    # cross-verify both directions
    bzip2 -dc "$f.lean.bz2" | cmp -s - "$f" || { echo "CROSS-DECODE FAILURE: $name"; exit 1; }
    "$BIN" -dc "$f.sys.bz2" | cmp -s - "$f" || { echo "OURS-DECODE FAILURE: $name"; exit 1; }
  else
    sys_ms=- ; sys_out=-
  fi
  if [ "$sys_out" != "-" ] && [ "$sys_out" != "0" ]; then
    rel=$((lean_out * 100 / sys_out))
  else
    rel=-
  fi
  printf '%-16s %12s %14s %14s %14s %14s %8s\n' \
    "$name" "$insize" "$lean_ms" "$lean_out" "$sys_ms" "$sys_out" "$rel"
done
echo
echo "ratio% = lean output size as a percentage of system bzip2's (lower is better; 100 = parity)"
