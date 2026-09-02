#!/usr/bin/env bash
# Regenerates the Effects-side parity receipt and compares it byte-for-byte
# with the committed receipt and with the committed source-side receipt taken
# from lean4-effect4 at the commit named in generated/algebra-parity.source.txt.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$(mktemp "${TMPDIR:-/tmp}/algebra-parity.XXXXXX")"
trap 'rm -f -- "$tmp"' EXIT
cd "$repo_root"
lake build Effects >/dev/null
PARITY_OUT="$tmp" lake env lean scripts/AlgebraParity.lean >/dev/null
cmp -s "$tmp" generated/algebra-parity.tsv || {
  echo "FAIL generated/algebra-parity.tsv drifted from the current Effects tree" >&2
  diff "$tmp" generated/algebra-parity.tsv | head -20 >&2; exit 1; }
cmp -s generated/algebra-parity.tsv generated/algebra-parity.source.tsv || {
  echo "FAIL Effects receipt differs from the lean4-effect4 source receipt" >&2
  diff generated/algebra-parity.tsv generated/algebra-parity.source.tsv | head -20 >&2; exit 1; }
rows="$(wc -l < generated/algebra-parity.tsv | tr -d ' ')"
echo "PASS algebra parity: $rows constants identical to $(cat generated/algebra-parity.source.txt)"
