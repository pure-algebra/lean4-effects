# Effects counterexample register

Stable IDs in this file are never reused. The eight algebra rows keep the IDs
they had in lean4-effect4 (`E4-ALG-CE-*`); the `origin` column records where
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
