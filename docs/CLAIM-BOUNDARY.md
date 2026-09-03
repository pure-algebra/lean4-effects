# What `Effects` claims, and what it does not

Status: adopted with slice S1 of the split, 2026-09-02. This document is the
repair for findings R1 and R3 of the lean4-effect4 review of 2026-09-02. It
fixes the boundary before the algebra modules arrive in S2, so that no
consumer reads more into a shared signature than the theorems state.

## Claimed

Every claim is a kernel-checked theorem over the structural carrier. Equality
of programs is Lean's structural equality of the inductive `Program`; there
is no behavioural quotient.

| Claim | Statement family | Hypotheses |
| --- | --- | --- |
| Constructor equations | `pure` and `vis` are the defining equations of `Program`; `bind` computes by structural recursion | none |
| Monad laws | `Program S` is a `LawfulMonad` | none |
| Interpretation | `interpret h` is the monad homomorphism induced by handler `h`; `interpret_pure`, `interpret_vis`, `interpret_perform`, `interpret_bind` | the target monad's left unit and associativity, or `LawfulMonad` in the convenience forms |
| Identity | `interpret identityHandler` is the identity; programs equal under every interpretation are equal | none |
| Sums | `Handler.sum` is characterised by its two projections and is unique; `Program.inl`/`inr` are injective monad morphisms; injection handlers compose to the identity | none beyond the sum's shared answer universe |
| Freeness and initiality | a monad morphism out of `Program S` that agrees with a handler on every one-operation program is `interpret` of that handler; `Program S` is initial among monads equipped with an `S`-handler | the target's monad equations, stated per theorem |
| Interpreter pin | the conjunction of pure/bind preservation and operation agreement pins the interpreter; neither half alone does | as above; the two halves are attacked by `E4-ALG-CE-002` and `003` |
| Towers | `Handler.through` composes across signatures; it is associative and unital; a monoid exists only on endomorphisms `Handler S (Program S)` | left unit and associativity of the bottom target |

## Not claimed

- **No equations on a signature.** `Signature` has operations and answer
  types. A standard's state invariants, operation equations, commutation of
  independent operations, scheduling behaviour, or trace relations are not
  carried by the signature and are not implied by `Signature.sum`. A sum
  supplies disjoint operations, nothing more.
- **No theorem transfer between handlers.** Two handlers for one signature
  are two models. A theorem proved about a program under one handler holds
  under another only if the theorem's hypotheses hold for that handler too.
  "Both are handlers for the same signature" is not such a hypothesis.
  Law satisfaction by an implementation, and conformance of a host to a
  standard's corpus, are separate downstream records with their own
  assumptions.
- **No behavioural equivalence.** The library proves structural equalities
  and equalities after interpretation into a stated target. It does not
  define bisimilarity, trace equivalence, or a quotient by any such relation,
  and it makes no congruence claim for one.
- **No serialization or identity.** `Program` stores Lean continuations. It
  is not stored program syntax, has no content hash or decidable equality,
  and is not the carrier for cycles, sharing, or block references
  (`E4-ALG-CE-007`). A first-order representation is a downstream carrier
  with its own embedding theorem.
- **No bounded-runner composition.** A fixed-fuel evaluator receives no bind
  law here (`E4-ALG-CE-006`). Composition is stated at `interpret`.
- **No finiteness.** `Program` is well-founded on every selected branch; it
  need not have finitely many nodes or a uniform depth bound
  (`E4-ALG-CE-008`).
- **No implicit universe lift.** An explicit signature map or universe lift
  is a separate packet with its own coherence laws.
- **No host correspondence.** Nothing here relates a program to a runtime,
  a generated artifact, or a test corpus.

## Where the rest lives

| Concern | Owner |
| --- | --- |
| Operation laws and observation relations for a particular standard | that standard's library, stated over its interpretation |
| State transport through a tower, explicit signature maps | a later `Effects` packet, opened only by a typed consumer example (S6) |
| First-order flow, relational semantics, logic, realizers, targets | lean4-effect4 and the standard libraries |
| Host admission and conformance | the consumer's host-profile records |

## Axiom admissions

The ceiling for every declaration under `Effects/` and `EffectsTest/` is
`propext` and `Quot.sound`. `Classical.choice` is admitted in exactly one
module, `EffectsTest.Audit.AxiomGate`, because `MetaM` reaches it. There are
no declaration-level admissions. A new admission is recorded here first and
in the gate second, and the gate fails if the admission goes stale.

## v0.2.0 additions

Three generic packets and one move, stood up 2026-09-02 ahead of their
contract packets (the proofs are the one-induction shapes the algebra
already uses; batteries follow):

- `Effects/Morphism.lean`: `Signature.Hom`, `Program.map`, `Handler.pull`,
  `interpret_map`, the sum isomorphisms and `Signature.empty`. The row normal
  form of a requirement set.
- `Effects/Transport.lean`: `MonadHom`, `Handler.mapHom`, `interpret_mapHom`,
  `interpretHom`, `through = mapHom (interpretHom ·)` by `rfl`, `MonadHom.stateT`.
  State transport through a tower.
- `Effects/Family.lean`: `Family`, `Family.toSignature`, `Family.Service` and
  its round trip with `Handler`, `Alphabet` and `Alphabet.toFamily`. The
  first-order carrier's embedding that the boundary above promised downstream.
- `Effects/Flow/*`: the generic first-order flow and its checked admission,
  moved from lean4-effect4 `de3e2ec` with only the namespace changed.

The claims of the nine algebra modules are unchanged; `generated/algebra-parity.tsv`
still holds.

## v0.3.0: the trace alphabet

`Effects/Trace.lean` adds one service-level observation vocabulary
(`Trace.Event`: operation with request and answer, failure, decision, region
entry and exit, finalizer with its outcome, outcome, frontier), masks as
projections (`m1` keeps operations, answers, failures and the outcome; `m2`
keeps everything), and `Family.Service.traced`, an around-wrapper that logs
each method's request and answer. Its law is `interpret_traced_fst`:
forgetting the log recovers the plain interpretation. Packet:
`test/contracts/trace.contract.md`; attacks `EF-TRACE-CE-001..003`.

v0.3.1 adds `Family.Service.tracedExcept` for the aborting error reading (a
service into `ExceptT ε M`, log outside the error) with the same projection
law, `interpret_tracedExcept_fst`.

Not claimed: any relation between a trace and a host, a frame machine, or a
scheduler; any behavioural equivalence. Agreement between two emitters of this
alphabet is a downstream, executable judgment under a named mask, and it is
stated in lean4-effect4 (`docs/TRACE-DAG.md`), never here. The module
traverses no `String`; rendering a trace to a wire form is a consumer's
admission.

## v0.4.0: first-order flows with block parameters

`Effects/Flow/{Block,Raw,Admission,Checked}.lean` re-freeze the flow admission
packet (`test/contracts/flow-v2.contract.md`, superseding the v1
`flow-admission` packet moved here in v0.2.0). A block now declares a
parameter list; a terminator names its operands by position (`Var`); `jump`
and `choose` pass argument lists; `perform` passes its arguments plus the
operation's answer. Admission has seventeen ordered clauses: the thirteen v1
clauses (operand typing is now `termTypeMismatch`) and `unknownVariable`,
`argumentArity`, `argumentTypeMismatch`, `unchosenCycle`. The last is the one
global clause: every cycle of the successor graph passes through a `choose`
(`CyclesWF`), decided by the kernel-computable `cyclesChoose` with its law
`cyclesChoose_iff`, so a finite decision tape bounds every run of an admitted
flow. Retained: `admit_sound`, `admit_complete`, `error_iff_not_wf`,
`error_iff_firstDiagnostic`, `admit_error_valid`, `diagnoseAt_some_valid`,
`FirstDiagnostic.valid` and `condemns`, `clause_all_complete`, the erase laws,
and `FlowWF.reachable_declared`. Attacks `EF-FLOW-CE-001..003`
(`test/counterexamples/flow/ATTACKS.md`). Sixteen named theorems have axiom
receipts in `EffectsTest/Flow/FlowV2AxiomReport.lean`; the union is
`propext` and `Quot.sound` (`reachable_declared`, `erase_wf`,
`CheckedFlow.erase_eq_raw`, and `CheckedFlow.ext` need only `propext`).

Not claimed: any run of a flow (the runner, its frontier, and the decision
tape live in lean4-effect4); regions and finalizers (a later bump); any
relation between a flow and a program, a trace, or a host.
