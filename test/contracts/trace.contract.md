# Trace contract

Status: FROZEN, builder-authored 2026-09-02; RE-FROZEN 2026-09-03 for v0.6.0
(light ceremony by operator ruling D2 of the trace plan: contract, battery and
code land together; a re-freeze of a frozen alphabet is D2's declared
exception, packet A1 of the reification plan).

Version note. v0.3.0 froze the alphabet; v0.3.1 added the fallible reading;
v0.6.0 widens `Trace.Outcome` by one constructor, `defect`, and adds
`Outcome.map` with `map_id` and `map_comp`. `Trace.Event` is unchanged in
shape, `Trace.Mask` is unchanged in shape, and every v0.3.x law is retained
verbatim, re-checked, and listed under ENSURES below. Nothing is removed and
no proposition is weakened.

Implementation fence: `Effects/Trace.lean`
Lean battery: `EffectsTest/Trace/TraceContract.lean`
Axiom report: `EffectsTest/Trace/AxiomReport.lean`
Counterexamples: `EF-TRACE-CE-001` through `EF-TRACE-CE-004` in
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
- `Trace.Outcome υ` (`success`, `failure`, `defect`, `interrupted`);
  `Outcome.map` (v0.6.0), a payload re-encoding with independent payload
  universes and no `ToVal` in its signature.
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
5. (v0.6.0) `Outcome.map_id` (`outcome.map id = outcome`) and
   `Outcome.map_comp` (`(outcome.map first).map second = outcome.map (second ∘
   first)`), both by cases on the four constructors and neither depending on
   any axiom.

Re-checked unchanged at v0.6.0. Widening `Outcome` touches no statement above:
`Mask.keeps` matches on an event's *kind* and never on the outcome an event
carries, so `Mask.m2_keeps`, `project_project`, `project_m2`, `project_m1_m2`
and `agree_of_agree_m2` are the same propositions with the same proofs, and
the four `interpret`/`Projects` laws never mention `Outcome` at all. The
battery holds an executable receipt that every mask in the packet
(`outcomeOnly`, `m1`, `m2`) keeps and drops `done`, `leave` and `finalizer`
identically for all four outcomes, and instantiates the projection laws on a
trace carrying a defect.

## Producers, and what this library does not emit

`Family.Service.traced` and `Family.Service.tracedExcept` emit `op`, `answer`
and `failed` rows only. No declaration in this library constructs
`Outcome.defect` or `Outcome.interrupted`, and none constructs `Event.done`,
`Event.leave`, `Event.finalizer`, `Event.decide`, `Event.enter` or
`Event.frontier`. Those constructors exist so that a downstream runner (a
first-order flow runner, a region runner) or a host bridge has a place to
land; the vocabulary is frozen here, the producers are not. In particular
v0.6.0 does not add an around-wrapper producing `Outcome.interrupted`: that
constructor and `defect` are produced only by runners and bridges downstream,
and this packet claims nothing about when either is correct to emit.

## Counterexample obligations

| ID | Frozen attack | Forced repair |
| --- | --- | --- |
| `EF-TRACE-CE-001` | tracing as `mapHom` of a lift | around-wrapper with `interpret_traced_fst` |
| `EF-TRACE-CE-002` | answers redundant given operations and outcome | `m1` keeps answers |
| `EF-TRACE-CE-003` | agreement on unprojected traces | agreement is per named mask |
| `EF-TRACE-CE-004` | a defect rendered as a failure (v0.6.0) | `Outcome.defect` is its own constructor, and no mask can recover the collapse |

## Trust and acceptance

`lake build` (gate), `./scripts/test-trust-gate.sh`, and every
`#print axioms` in the report within `propext`/`Quot.sound`. The module
traverses no `String`; rendering to a wire form is a consumer's admission.
