# Algebra proof graph

Status: closed, 2026-09-02. This is the proof graph for the nine modules
under `Effects/Algebra/`, derived from the two moved contracts and the
sixty named receipts in `EffectsTest/Algebra/AxiomReport.lean`. Nothing from
lean4-effect4's design basis about first-order flow, relational semantics,
logic, or targets is carried over; those edges belong to their owners.

Every theorem named here reaches at most `propext` and `Quot.sound`; the
exhaustive gate in `EffectsTest/Audit/AxiomGate.lean` re-checks that on every
build, and `generated/algebra-parity.tsv` records the axiom set of every one
of the 215 compiled constants.

| Edge | Obligation | Closed by | Attacked by |
| --- | --- | --- | --- |
| A1 identity | `Signature`, `Program`, `Handler` are the only carriers; `ModelMorphism` bundles an existing map and `IsMonadMorphism` without a second morphism notion | `ModelMorphism.toIsMonadMorphism`, `ModelMorphism.ext`, `ModelMorphism.ofIsMonadMorphism_map`, `ModelMorphism.ofIsMonadMorphism_toIsMonadMorphism` | `E4-ALG-CE-007` (no first-order identity is claimed) |
| A2 construction | `pure` and `vis` are the defining equations; `bind` is structural; `Handler.ext` | `Program.perform_bind`, `Handler.ext` | — |
| A3 monad laws | `Program S` is a lawful monad | `Program.bind_pure_right`, `Program.bind_assoc`, the `LawfulMonad (Program S)` instance | — |
| A4 interpretation | `interpret` is a monad homomorphism under the target's equations | `interpret_pure`, `interpret_vis`, `interpret_perform`, `interpret_perform_of_rightUnit`, `interpret_bind`, `interpret_bind_of_equations`, `leftUnit_of_lawful`, `rightUnit_of_lawful`, `bindAssoc_of_lawful` | `E4-ALG-CE-006` (no fixed-fuel bind law) |
| A5 identity handler | interpreting through the syntactic identity is the identity; separation by all interpretations | `interpret_identity`, `Program.eq_of_all_interpretations` | — |
| A6 sums | projections, uniqueness, injective injections, injection handlers, and their one-target and all-models equivalences | `Handler.sum_handle_inl`, `Handler.sum_handle_inr`, `Handler.sum_unique`, `interpret_inl`, `interpret_inr`, `Program.inl_pure`, `Program.inr_pure`, `Program.inl_bind`, `Program.inr_bind`, `Program.inl_injective`, `Program.inr_injective`, `Program.inl_unique`, `Program.inr_unique`, `Program.inl_one_target_iff`, `Program.inr_one_target_iff`, `Program.inl_unique_one_target`, `Program.inr_unique_one_target`, `Program.inl_all_models_iff`, `Program.inr_all_models_iff`, `Program.inl_unique_all_models`, `Program.inr_unique_all_models`, `interpret_leftInjectionHandler`, `interpret_rightInjectionHandler`, `injectionHandlers_sum` | `E4-ALG-CE-001` |
| A7 freeness and initiality | a morphism agreeing with a handler on operations is that handler's interpretation; initiality among `S`-models, in both quantifier orders | `interpret_isMonadMorphism`, `interpret_isMonadMorphism_of_equations`, `interpret_of_isMonadMorphism`, `exists_handler_of_isMonadMorphism`, `handler_eq_of_interpret_operation_eq`, `handler_eq_of_interpret_eq`, `program_is_free`, `program_is_initial_in_models`, `program_is_initial_in_models_eq` | `E4-ALG-CE-003` (not initial among bare monads) |
| A8 interpreter pin | pure/bind preservation together with operation agreement pins the interpreter, and the pin is inhabited | `interpret_pinned`, `interpret_inhabits_the_pin` | `E4-ALG-CE-002`, `E4-ALG-CE-003` |
| A9 towers | `through` collapses an implementation; associative and unital across signatures; a monoid on endomorphisms | `interpret_through`, `interpret_through_of_equations`, `Handler.through_assoc`, `Handler.through_identity_right`, `Handler.through_identity_left`, `Handler.through_endomorphism_monoid` | `E4-ALG-CE-004` |
| A10 universes | independent operation and answer universes; results in the answer universe; no implicit lift | the declared universe signatures, frozen by `EffectsTest/Algebra/ExtractionContract.lean` | `E4-ALG-CE-005`, `E4-ALG-CE-008` |

Open edges: none within this package. Explicit signature maps, state
transport through a tower, and any universe lift are deliberately outside
it (`docs/CLAIM-BOUNDARY.md`, "Where the rest lives").
