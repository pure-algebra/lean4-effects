# Trace contract

Status: FROZEN, builder-authored 2026-09-02 (light ceremony by operator ruling
D2 of the trace plan: contract, battery and code land together).
Implementation fence: `Effects/Trace.lean`
Lean battery: `EffectsTest/Trace/TraceContract.lean`
Axiom report: `EffectsTest/Trace/AxiomReport.lean`
Counterexamples: `EF-TRACE-CE-001` through `EF-TRACE-CE-003` in
  `test/counterexamples/REGISTER.md`; witnesses in
  `EffectsTest/Counterexamples/Trace/Around.lean`; attack shapes in
  `test/counterexamples/trace/ATTACKS.md`
Proof graph: `TRACE-PG-AGREEMENT` in lean4-effect4 `docs/TRACE-DAG.md`

## Claim boundary

The packet freezes one service-level observation alphabet, its masks as
projections, and one law: forgetting the log of a traced service recovers the
plain interpretation. It does not relate a trace to any host, does not define
behavioural equivalence, and does not compare a trace with the frame or
scheduler alphabets of lean4-effect4.

## Frozen declarations

- `Trace.Val` (eight constructors), `Trace.ToVal` with instances for `Unit`,
  `Nat`, `Int`, `Bool`, `String`, `Val`, products, `Option`, `List`, `Except`.
- `Trace.Outcome υ` (`success`, `failure`, `interrupted`).
- `Trace.Event ω υ δ ρ` (`op`, `answer`, `failed`, `decide`, `enter`, `leave`,
  `finalizer`, `done`, `frontier`).
- `Trace.Mask` (seven booleans), `Mask.keeps`, `Mask.outcomeOnly`, `Mask.m1`,
  `Mask.m2`, `Trace.project`.
- `Family.Service.traced`, `Handler.Projects`; (v0.3.1) `Family.Service.tracedExcept`, `Handler.ProjectsExcept`.

Binder names may differ; names, universes, argument roles, constructor fields and
theorem propositions are frozen by the battery's ascriptions.

## ENSURES

Proved without `sorry`, custom axioms, `partial`, `unsafe`, or
`Classical.choice`:

1. `project_project`, `project_m2`, `project_m1_m2`, `agree_of_agree_m2`.
2. `interpret_projects_fst`: a projecting handler into `StateT σ M` interprets
   to the plain handler after forgetting the state (`LawfulMonad M`).
3. `Family.Service.traced_projects`, `Family.Service.interpret_traced_fst`,
   `Family.Service.traced_perform`.
4. (v0.3.1) `Family.Service.tracedExcept` for a service into `ExceptT ε M`,
   with the log outside the error so a failed operation still records its
   request and a `failed` row; `Handler.ProjectsExcept`,
   `interpret_projectsExcept_fst`, `Family.Service.tracedExcept_projects`,
   `Family.Service.interpret_tracedExcept_fst`.

## Counterexample obligations

| ID | Frozen attack | Forced repair |
| --- | --- | --- |
| `EF-TRACE-CE-001` | tracing as `mapHom` of a lift | around-wrapper with `interpret_traced_fst` |
| `EF-TRACE-CE-002` | answers redundant given operations and outcome | `m1` keeps answers |
| `EF-TRACE-CE-003` | agreement on unprojected traces | agreement is per named mask |

## Trust and acceptance

`lake build` (gate), `./scripts/test-trust-gate.sh`, and every
`#print axioms` in the report within `propext`/`Quot.sound`. The module
traverses no `String`; rendering to a wire form is a consumer's admission.
