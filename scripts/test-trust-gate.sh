#!/usr/bin/env bash
# Exercises whether the trust gate rejects an authored trust token, a bodyless
# `opaque`, and an unadmitted `Classical.choice`.
#
# The detector is an elaboration-time check in the root aggregator
# `EffectsTest.lean`, which Lake builds LAST. Any earlier module that fails to
# build prevents the detector from running at all. So this gate does not
# tolerate a red module; it EXCISES the declared red modules from its
# throwaway probe copy, after first verifying that they are exactly the
# modules that fail.
#
# Ported from lean4-effect4 `scripts/test-trust-gate.sh` with the tree names
# changed and the Effect4 target-renderer planting step replaced by a plant
# into the `Effects` root, which is always present.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effects-test-trust.XXXXXX")"
project_root="$tmp_root/project"
audit_source="$project_root/EffectsTest/Audit/AxiomGate.lean"
audit_original="$tmp_root/AxiomGate.lean"
known_red="$repo_root/test/fixtures/trust-gate/known-red.txt"

cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

mkdir -p "$project_root"
cp "$repo_root/lakefile.toml" "$repo_root/lake-manifest.json" \
  "$repo_root/lean-toolchain" "$repo_root/Effects.lean" \
  "$repo_root/EffectsTest.lean" "$project_root/"
cp -R "$repo_root/EffectsTest" "$project_root/"
if [[ -d "$repo_root/Effects" ]]; then
  cp -R "$repo_root/Effects" "$project_root/"
fi

build_log="$tmp_root/build.log"

failing_targets() {
  awk '
    /^Some required targets logged failures:/ { collecting = 1; next }
    collecting && /^- / { print substr($0, 3); next }
    collecting && $0 !~ /^- / { collecting = 0 }
  ' "$1" | LC_ALL=C sort -u
}

declared_red="$( { [[ -f "$known_red" ]] && grep -v '^[[:space:]]*#' "$known_red" \
  | grep -v '^[[:space:]]*$' || true; } | LC_ALL=C sort -u )"

# --- 0. establish that the declared red set is exactly the failing set ------
(cd "$project_root" && lake build) >"$build_log" 2>&1 || true
observed_red="$(failing_targets "$build_log")"
if [[ -n "$declared_red" ]]; then
  observed_red="$(printf '%s\n' "$observed_red" | grep -v '^EffectsTest$' || true)"
fi
if [[ "$observed_red" != "$declared_red" ]]; then
  echo "FAIL the declared red set does not match the modules that actually fail" >&2
  echo "--- failing but not declared in test/fixtures/trust-gate/known-red.txt ---" >&2
  comm -23 <(printf '%s\n' "$observed_red") <(printf '%s\n' "$declared_red") >&2
  echo "--- declared red but actually green; remove the stale entry ---" >&2
  comm -13 <(printf '%s\n' "$observed_red") <(printf '%s\n' "$declared_red") >&2
  tail -60 "$build_log" >&2
  exit 1
fi

# --- 1. excise the declared red modules from the probe copy ----------------
excised=0
if [[ -n "$declared_red" ]]; then
  while IFS= read -r module; do
    [[ -n "$module" ]] || continue
    relative="${module//.//}.lean"
    target="$project_root/$relative"
    if [[ ! -f "$target" ]]; then
      echo "FAIL declared red module has no source file: $relative" >&2
      exit 1
    fi
    rm -f -- "$target"
    excised=$((excised + 1))
    echo "NOTE excised declared red module from the probe copy: $module"
  done <<<"$declared_red"
  while IFS= read -r module; do
    [[ -n "$module" ]] || continue
    grep -v "^import ${module}$" "$project_root/EffectsTest.lean" \
      >"$project_root/EffectsTest.lean.tmp"
    mv "$project_root/EffectsTest.lean.tmp" "$project_root/EffectsTest.lean"
  done <<<"$declared_red"
fi

cp "$audit_source" "$audit_original"

expect_acceptance() {
  local label="$1"
  if ! (cd "$project_root" && lake build) >"$build_log" 2>&1; then
    echo "trust-gate self-test unexpectedly rejected $label" >&2
    tail -80 "$build_log" >&2
    exit 1
  fi
  echo "PASS trust gate accepted $label"
}

expect_rejection() {
  local fixture="$1"
  local expected_modifier="$2"
  local label="$3"
  cp "$audit_original" "$audit_source"
  printf '\n' >>"$audit_source"
  sed -n '1,$p' "$fixture" >>"$audit_source"
  if (cd "$project_root" && lake build) >"$build_log" 2>&1; then
    echo "trust-gate self-test unexpectedly accepted $label" >&2
    exit 1
  fi
  if ! grep -Fq "contains an authored \`$expected_modifier\` trust token" "$build_log"; then
    echo "trust-gate self-test rejected $label for an unexpected reason" >&2
    tail -80 "$build_log" >&2
    exit 1
  fi
  echo "PASS planted $label rejected"
}

expect_acceptance "the unmodified source tree"

cp "$audit_original" "$audit_source"
printf '\n' >>"$audit_source"
sed -n '1,$p' "$repo_root/test/fixtures/trust-gate/benign.lean.txt" >>"$audit_source"
expect_acceptance "comments, strings, and numeric projections"

expect_rejection "$repo_root/test/fixtures/trust-gate/partial.lean.txt" partial \
  "partial declaration"
expect_rejection "$repo_root/test/fixtures/trust-gate/unsafe.lean.txt" unsafe \
  "unsafe declaration"
# The four tokens the source pass exists for: each is written inside an
# `example` or as a declaration the compiled-environment pass cannot see, or
# cannot see in time.
expect_rejection "$repo_root/test/fixtures/trust-gate/sorry.lean.txt" sorry \
  "sorry inside an example"
expect_rejection "$repo_root/test/fixtures/trust-gate/native-decide.lean.txt" native_decide \
  "native_decide inside an example"
expect_rejection "$repo_root/test/fixtures/trust-gate/axiom.lean.txt" axiom \
  "axiom declaration"

# --- 1b. a bodyless `opaque` is a declaration-level refusal -----------------
cp "$audit_original" "$audit_source"
printf '\n' >>"$audit_source"
cat "$repo_root/test/fixtures/trust-gate/opaque.lean.txt" >>"$audit_source"
if (cd "$project_root" && lake build) >"$build_log" 2>&1; then
  echo "trust-gate self-test unexpectedly accepted a bodyless opaque" >&2
  exit 1
fi
if ! grep -Fq 'is an `opaque` with no body' "$build_log"; then
  echo "trust-gate self-test rejected the bodyless opaque for an unexpected reason" >&2
  tail -80 "$build_log" >&2
  exit 1
fi
echo "PASS planted bodyless opaque rejected"

# --- 2. an unadmitted Classical.choice in the production tree is rejected --
cp "$audit_original" "$audit_source"
root_source="$project_root/Effects.lean"
cp "$root_source" "$tmp_root/Effects.lean"
printf '\n' >>"$root_source"
cat "$repo_root/test/fixtures/trust-gate/unadmitted-choice.lean.txt" >>"$root_source"
if (cd "$project_root" && lake build) >"$build_log" 2>&1; then
  echo "trust-gate self-test unexpectedly accepted an unadmitted choice dependency" >&2
  exit 1
fi
if ! grep -Fq 'declaration Effects.plantedUnadmittedChoice reaches unexpected axiom Classical.choice' "$build_log"; then
  echo "trust-gate self-test rejected the choice dependency for an unexpected reason" >&2
  tail -80 "$build_log" >&2
  exit 1
fi
echo "PASS unadmitted choice dependency in the production tree rejected"
cp "$tmp_root/Effects.lean" "$root_source"
expect_acceptance "restored source tree"

# Reuse the built probe project for lexical failures that Lean compilation
# would otherwise reject before the source detector gets to inspect them.
"$repo_root/scripts/test-source-trust-tokenizer.sh" "$project_root"

if [[ "$excised" -gt 0 ]]; then
  echo "NOTE $excised declared red module(s) were excised before testing; the trust"
  echo "NOTE property is therefore unverified FOR THOSE MODULES until they build"
fi
