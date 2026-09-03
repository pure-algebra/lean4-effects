# Effects counterexample register

Stable IDs in this file are never reused. The eight algebra rows keep the IDs
they had in lean4-effect4 (`E4-ALG-CE-*`); rows minted here use the family
`EF-<AREA>-CE-NNN`; the `origin` column records where
each row came from and the `disposition` column records how its witness is
reviewable from a clean checkout of this repository:

- `ported executable witness` — a Lean module in this repository attacks the
  statement and is reached by the default build;
- `retained external evidence` — the witness is a source span in another
  repository at an immutable commit, identified by path, span, and
  whole-file SHA-256, and is not reproduced here;
- `design row` — the attacked statement is a representation decision, not a
  theorem; the witness is the cited design text.

`status` is the row's original status at the origin: `SEEDED` (the packet
froze the attack with a local witness) or `PINNED` (the witness was in
Foldlab at the named commit). A row closes only when its witness is retained
and the repaired declaration or theorem mechanically rejects the attack.

Foldlab evidence is cited at commit `feb29321fd50204aa338209d313e84a3f8b71c66`
(`library/cas/Cas/Backend/Universal.lean`, whole-file SHA-256
`cce4f2a50a7e2a2e8b57b4de1a82f90c86efcb9749683795fd2b9e96d2ad8010`;
`library/cas/Cas/Lang/Prog.lean`, SHA-256
`a8ac15632d155f9558db1969f2a25faf548e337c35b584f54316d5aba0f958aa`), under
Foldlab's Apache-2.0 license. Effects does not import Foldlab.

| ID | Status | Attacked statement | Witness / evidence | Forced repair | Origin | Disposition |
| --- | --- | --- | --- | --- | --- | --- |
| `E4-ALG-CE-001` | SEEDED | Handler sum can be characterized by one arm or by examples | `EffectsTest/Algebra/ExtractionContract.lean`, `swappedSum`, differs on both arms | require both projection equations and `Handler.sum_unique` | lean4-effect4 `217d3e4` | ported executable witness |
| `E4-ALG-CE-002` | PINNED | Monad-morphism laws alone pin an interpreter | Foldlab `Universal.lean:701–714`, `pinned_needs_op_agreement`; re-derived as `EffectsTest/Counterexamples/Algebra/InterpreterPin.lean`, `morphism_alone_does_not_pin` | require agreement with the supplied handler on every one-operation program | lean4-effect4 `217d3e4`; Foldlab pin | ported executable witness (re-derived; Foldlab span retained as provenance) |
| `E4-ALG-CE-003` | PINNED | Operation agreement alone pins an interpreter; or `Program S` is initial among bare monads | Foldlab `Universal.lean:716–727`, `pinned_needs_the_morphism_law`, plus its two distinct state morphisms; re-derived as `EffectsTest/Counterexamples/Algebra/InterpreterPin.lean`, `agreement_alone_does_not_pin` | require both pure/bind preservation and operation agreement; state initiality only in the category of `S`-models | lean4-effect4 `217d3e4`; Foldlab pin | ported executable witness (re-derived; Foldlab span retained as provenance) |
| `E4-ALG-CE-004` | PINNED | All handler towers form one monoid | Foldlab `Universal.lean:739–790`: composition changes source/target signatures; only `Handler S (Program S)` is closed; re-derived as `EffectsTest/Counterexamples/Algebra/TowerCategory.lean`, a guarded rejection of `twoToThree.through twoToThree` beside the typed cross-signature composite | state a category across signatures and a monoid only on endomorphisms | lean4-effect4 `217d3e4`; Foldlab pin | ported executable witness (re-derived; Foldlab span retained as provenance) |
| `E4-ALG-CE-005` | SEEDED | Program result universes may vary independently of the signature answer and handler input universe | guarded rejection of `Program SmallSignature Type` in `EffectsTest/Algebra/ExtractionContract.lean` | align the three universes; add only explicit, law-carrying lifts later | lean4-effect4 `217d3e4` | ported executable witness |
| `E4-ALG-CE-006` | PINNED | A fixed-fuel evaluator admits a bind/composition law | Foldlab `Universal.lean:894–910`, `run_has_no_composition_law` over the CAS word store; re-derived generically as `EffectsTest/Counterexamples/Algebra/FixedFuel.lean`, `run_has_no_composition_law` | state composition at `interpret`/big-step, never at one fixed fuel | lean4-effect4 `217d3e4`; Foldlab pin | ported executable witness (re-derived; Foldlab span retained as provenance) |
| `E4-ALG-CE-007` | PINNED | The higher-order proof carrier is canonical first-order program content | Foldlab `Prog.lean:12–15`: continuations are host functions and are not serializable; `docs/DESIGN-BASIS.md` DB-01 and `docs/CLAIM-BOUNDARY.md` "No serialization or identity" | keep `Program` as proof syntax; introduce a distinct checked first-order flow with an explicit embedding | lean4-effect4 `217d3e4`; Foldlab pin | design row |
| `E4-ALG-CE-008` | SEEDED | Inductiveness makes every `Program` a globally finite tree | `EffectsTest/Algebra/ExtractionContract.lean`: a `Nat`-indexed injective continuation has distinct children of unbounded finite depth | describe `Program` as a well-founded higher-order W-tree; claim only selected-branch well-foundedness, not finite branching or a uniform depth bound | lean4-effect4 `217d3e4` | ported executable witness |
| `EF-TRACE-CE-001` | SEEDED | A tracing handler is `Handler.mapHom` of a monad homomorphism | `EffectsTest/Counterexamples/Trace/Around.lean`, `mapHom_logs_nothing`: the lift-transported handler runs `incr` with an empty log | tracing is an around-wrapper (`Family.Service.traced`); its law is `interpret_traced_fst` | this repository, v0.3.0 | ported executable witness |
| `EF-TRACE-CE-002` | SEEDED | Operation order plus outcome determines a run, so answers are redundant | `Around.lean`, `answers_separate_what_ops_do_not`: services answering 41 and 5 agree on operations and outcome | `Mask.m1` keeps `answer` and `failed` rows | this repository, v0.3.0 | ported executable witness |
| `EF-TRACE-CE-003` | SEEDED | Agreement may be checked on unprojected traces | `Around.lean`, `agreement_is_per_mask`: equal under `m1`, different raw and under `m2` | every agreement names its mask; `agree_of_agree_m2` is the only refinement direction | this repository, v0.3.0 | ported executable witness |
| `EF-FLOW-CE-001` | SEEDED | One typed payload per block is enough first-order flow content; `perform` may replace it with the answer | design row: `Effects/Flow/Block.lean` and `Raw.lean` at `9595a88` (v0.3.1), `RawTerm.perform (operation) (target)` with `RawBlock.inputTy` typed by the answer, so `let x ← get; put x; return x` has no block holding `x` across `put`; repair witness `EffectsTest/Counterexamples/Flow/FlowV2.lean`, `incr` admitted and `incrDropped` rejected (red until Flow v2 lands) | block parameter lists; `perform`'s target receives `args ++ [answer]`; `ret` and the request name a `Var` | this repository, v0.4.0 | design row (v0.3.1 text) with a ported executable repair witness |
| `EF-FLOW-CE-002` | SEEDED | A finite decision tape bounds every run of an admitted flow without a cycle clause | v0.3.1 `admit` accepts a `jump` self-loop: transcript in `test/counterexamples/flow/ATTACKS.md` run 2026-09-02 against `9595a88`, and lean4-effect4 `c951711` `Effect4Test/Flow/AdmissionContract.lean:531–538` `selfCycleFlow` (`E4-FLOW-CE-005`); v2 witness `FlowV2.lean`, `unchosenLoop` rejected with `unchosenCycle` at `.block 0` while `chosenLoop` admits (red until Flow v2 lands) | `CyclesWF`: every cycle passes through a `choose`; clause `unchosenCycle`; `cyclesChoose_iff` | this repository, v0.4.0 | retained external evidence (v1 admission at immutable commits) with a ported executable repair witness |
| `EF-FLOW-CE-003` | SEEDED | Argument arity can be checked without types | `FlowV2.lean`, `rightArityWrongType`: `diagnoseAt … .argumentArity = none` and `admit` fails with `argumentTypeMismatch` at `.argument ⟨0⟩ 0 0`; converse `wrongArity` (red until Flow v2 lands) | `argumentTypeMismatch` is a separate positional clause after `argumentArity`, with a site naming block, receiver, and position | this repository, v0.4.0 | ported executable witness |
