#!/usr/bin/env bash
# Exercise the production private tokenizer without a whole-tree build or
# exporting an audit API. The temporary copy appends tests in its namespace.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
project_root="$(cd "${1:-$repo_root}" && pwd)"
tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effects-source-trust.XXXXXX")"
trap 'rm -rf -- "$tmp_root"' EXIT

cp "$project_root/EffectsTest/Audit/AxiomGate.lean" "$tmp_root/SourceTrustTokenizer.lean"
cat >>"$tmp_root/SourceTrustTokenizer.lean" <<'LEAN'

namespace EffectsTest.Audit

run_elab do
  let some fixtureDirectory ← liftM <| IO.getEnv "EFFECTS_SOURCE_TRUST_FIXTURES"
    | throwError "missing tokenizer fixture directory"
  let environment ← Lean.getEnv
  let cases : Array (String × Except Unit (Option String)) := #[
    ("benign.lean.txt", .ok none),
    ("partial.lean.txt", .ok (some "partial")),
    ("unsafe.lean.txt", .ok (some "unsafe")),
    ("sorry.lean.txt", .ok (some "sorry")),
    ("native-decide.lean.txt", .ok (some "native_decide")),
    ("axiom.lean.txt", .ok (some "axiom")),
    ("malformed-comment.lean.txt", .error ()),
    ("malformed-string.lean.txt", .error ()),
    ("malformed-raw-string.lean.txt", .error ()),
    ("malformed-decimal.lean.txt", .error ())
  ]
  let mut failures : Array String := #[]
  for (fixture, expected) in cases do
    let path := System.FilePath.mk fixtureDirectory / fixture
    let result : Except String (Option String) ← liftM <| do
      try
        return .ok (← forbiddenTrustToken? environment path)
      catch error =>
        return .error error.toString
    let accepted := match expected, result with
      | .ok expectedToken, .ok observedToken => expectedToken == observedToken
      | .error (), .error message => message.startsWith "Effects source trust gate: tokenization failed"
      | _, _ => false
    if accepted then
      logInfo m!"PASS source tokenizer {fixture}"
    else
      failures := failures.push s!"{fixture}: expected {repr expected}, observed {repr result}"
  unless failures.isEmpty do
    throwError "source tokenizer regression(s):\n{String.intercalate "\n" failures.toList}"

end EffectsTest.Audit
LEAN

cd "$project_root"
EFFECTS_SOURCE_TRUST_FIXTURES="$repo_root/test/fixtures/trust-gate" \
  lake env lean "$tmp_root/SourceTrustTokenizer.lean"
