# Effects Lean-test routing

This boundary contains executable Lean attacks, examples, and proof receipts.
The repository root rules remain in force.

## Breaker ownership

A breaker freezes a contract and its red battery before the corresponding
implementation, and lists the red module in
`test/fixtures/trust-gate/known-red.txt`. A builder may repair test
elaboration without changing the attacked statement, witness, or acceptance
condition, but does not weaken or delete a breaker-owned test.

Every counterexample that can alter a declaration receives a stable ID in
`test/counterexamples/REGISTER.md`. The executable witness lives under
`EffectsTest/Counterexamples/<Area>/` and is linked from the register and the
owning contract. Keep the witness after the implementation rejects it.

## Evidence classes

Tests distinguish theorem evidence from finite executable probes. A passing
example does not become a general law. Axiom reports cover every exported
theorem and record actual dependencies; `EffectsTest/Algebra/AxiomReport.lean`
imports only the `Effects` library root.

## Audit modules

`EffectsTest/Audit/AxiomGate.lean` is audit implementation and is the only
module admitted to reach `Classical.choice`. A test file that needs `MetaM`
is added to the gate's exact-module list with its reason, never by prefix.

Before handoff, run the narrow file directly and the default Lake build.
