# Flow v3 contract packet

Status: FROZEN / GREEN, landed 2026-09-03

Implementation fence: `Effects/Flow/{Block,Raw,Admission,Checked}.lean`

Battery: `EffectsTest/Flow/FlowV3Contract.lean` (kernel receipts:
ascriptions, `rfl`, `Iff.rfl`, `decide`, `#guard` over `admit`). The retained
v2 surface stays pinned in `EffectsTest/Flow/FlowV2Contract.lean`, re-spelled
where v3 changed it.

Axiom report: `EffectsTest/Flow/FlowV2AxiomReport.lean` (unchanged list; the
sixteen named theorems are re-proved over the wider carrier and keep the
`propext` / `Quot.sound` ceiling).

Counterexamples: `test/counterexamples/REGISTER.md`, rows `EF-FLOW-CE-007`
and `EF-FLOW-CE-008`; witnesses in
`EffectsTest/Counterexamples/Flow/FlowV3.lean`; attack shapes in
`test/counterexamples/flow/ATTACKS.md`.

Version: this packet is Effects v0.7.0. It **supersedes the terminator list
and the two edge clauses of `test/contracts/flow-v2.contract.md`**; every
other frozen declaration of that packet stands, and its counterexample rows
`EF-FLOW-CE-001..003` are retained with their sites. The region packet
`test/contracts/flow-regions.contract.md` (v0.5.0) is unchanged: the region
layer reads terminators only through `RawTerm.successors`, so both new
terminators pass its clauses without a new rule.

## Claim boundary

Flow v2 gives every block a parameter list and four terminators. Two shapes
have no first-order spelling in it.

The first is a *caught* failure. A v2 `perform` names one successor, so the
only reading of an operation that fails is that the whole flow fails; a flow
cannot name the block that a failure continues at, and `try/catch`,
retry-on-error, and requeue-on-error have no shape. Flow v3 adds
`performCatch`, a `perform` with a second, failure successor. Its two edges
carry *different* argument lists and *different* arities, which is why
`RawTerm.argsAt` and `RawTerm.arityAt` are keyed by the position of the edge
in `RawTerm.successors` rather than by the terminator alone, and why the two
edge clauses (`argumentArity`, `argumentTypeMismatch`) are re-stated over the
edge index.

The second is a test of a computed value. A v2 `choose` is answered by the
decision tape, so "loop while the queue is non-empty" can only be spelled as
an unconstrained nondeterministic choice: the value that decides it is
invisible to the carrier. Flow v3 adds `branch`, taken by the *value* of its
test operand — and still a decision *site*. `RawTerm.isChoose` is true for
it, `RawTerm.decision?` names its site, so `CyclesWF` counts a branch loop
and a finite tape still bounds every run of an admitted flow. The test
operand carries the alphabet's own boolean spelling, `FlowAlphabet.boolTy`,
checked by the one clause v3 adds.

This packet freezes the carrier with those two terminators, the alphabet's
two new rows (`errorTy`, `boolTy`), the eight well-formedness clauses with a
five-fold `TermsWF`, the **eighteen** ordered admission clauses with exact
witnesses, and the retained admission theorems over the wider carrier.

Not claimed:

- **No execution semantics, again.** This packet defines no run, no decision
  tape, no evaluator. That a `performCatch` continues at its value successor
  on `.ok` and at its failure successor on `.error`, that a caught failure
  does not unwind an enclosing region, that a `branch` is taken by the value
  and refuses a run whose tape disagrees with it, and that the trace of a
  caught failure is `op` then `failed` then the successor's rows and never
  `done failure` — all four are the *design intent* the carrier is shaped
  for, and all four are theorems of lean4-effect4's runner and denotation,
  never of this library. What is claimed here is only that the carrier can
  express each shape and that admission types it.
- **No error algebra.** `FlowAlphabet.errorTy` is one type per operation. The
  boundary never reads the spelling an operation that cannot fail declares;
  it only compares. There is no empty type, no error sum, no subtyping, and
  no relation between an operation's error type and any host error.
- **No boolean semantics.** `FlowAlphabet.boolTy` is a spelling in the
  consumer's own `Ty`. Nothing here says that a value of that type has two
  inhabitants, that the two `branch` successors are exhaustive, or how a
  value of it is computed; the boolean atoms (`isZero`, `lt`, …) are ordinary
  alphabet operations of the consumer.
- **No unwinding, no finalizers.** A `performCatch` inside a region is
  admitted exactly when both of its successors carry the block's own region
  label (`successorLabel`, v0.5.0). This packet adds no release, no
  finalizer, and no rule about the order of either.
- **No reachability coverage,** no elaboration to `Program`, no handlers, no
  host correspondence, no TypeScript — as in v2.

## Design basis

- A terminator's successors are its block targets in source order. For
  `performCatch` the order is `[target, onError]`: **edge `0` is the value
  edge and edge `1` is the failure edge**, and that index is what `argsAt`
  and `arityAt` key on. For `branch` the order is `[onTrue, onFalse]`.
- `args` and `arity` remain the *value* edge's, so every v2 shape reads
  exactly as it did: `argsAt term 0 = args term`, `arityAt term 0 =
  arity term`, and off edge `1` every terminator supplies its value list
  (`argsAt_zero`, `arityAt_zero`, `argsAt_of_ne_one`, `arityAt_of_ne_one`).
- The failure successor receives `errorArgs ++ [error]`, so its arity is
  `errorArgs.length + 1` and its last parameter carries
  `alphabet.errorTy operation`. The value successor is unchanged from
  `perform`: `args ++ [answer]`, last parameter `alphabet.answerTy operation`.
- A `performCatch` performs an operation (`operation?`, `request?`) and is
  not a decision (`isChoose` is false, `decision?` is none). A `branch`
  performs no operation and *is* a decision (`isChoose` true, `decision?`
  some), so decision identities collide across `choose` and `branch` alike
  under `duplicateDecisionId`.
- The branch test is the one operand checked against the *alphabet's* own
  type vocabulary rather than against the flow's declared types or an
  operation's row, which is why it is a clause of its own (`BranchTestWF`,
  `branchTestType`) and not an arm of `OperandsWF` / `termTypeMismatch`.
- Payload orientation is the v2 rule, extended: a target block's parameter
  list is always the `actual` side; the `expected` side is what flows into it
  — the sender's argument types, the operation's answer type on the value
  edge, the operation's **error** type on the failure edge, and for the
  branch test the alphabet's `boolTy`.

## REQUIRES

1. Lean core and Std at the repository's pinned Lean 4.33.1 toolchain; no
   third-party Lake dependency. (v2 REQUIRES 1.)
2. `Ty` has decidable equality at the admission boundary; universes are as in
   v2 (`FlowAlphabet.{uTy, uOp}`, `CheckedFlow` in `Type uTy`). `errorTy` and
   `boolTy` add no class constraint and no universe.
3. `cyclesChoose` still needs no `DecidableEq Ty` and still inspects only
   identities and terminators; it counts a `branch` because `isChoose` does.
   (v2 REQUIRES 3.)
4. `cyclesChoose` is kernel-computable by structural recursion, so `decide`
   closes `cyclesChoose raw = true` on a concrete flow. (v2 REQUIRES 4.)

## Frozen declarations

Binder names may differ. Names, universes, argument roles, constructor
fields, result types, and theorem propositions are frozen by the battery's
ascriptions; the receipts marked `rfl` / `Iff.rfl` freeze the stated bodies
definitionally.

### D1 — the alphabet gains two rows (`Effects/Flow/Block.lean`)

```lean
structure FlowAlphabet.{uTy, uOp} (Ty : Type uTy) where
  -- id, Op, operationId, lookup, requestTy, answerTy as in v2
  errorTy : Op → Ty
  boolTy : Ty
  -- lookup_operationId, operationId_of_lookup as in v2
```

`errorTy operation` is the type of the value a `performCatch` binds in the
last slot of its failure successor. `boolTy` is the spelling a `branch` test
operand must carry.

### D2 — two terminators, and successor-indexed projections

```lean
inductive RawTerm where
  | ret (value : Var)
  | jump (target : BlockId) (args : List Var)
  | perform (operation : OperationId) (request : Var) (target : BlockId) (args : List Var)
  | choose (decision : DecisionId) (left right : BlockId) (args : List Var)
  | performCatch (operation : OperationId) (request : Var) (target : BlockId)
      (args : List Var) (onError : BlockId) (errorArgs : List Var)
  | branch (test : Var) (site : DecisionId) (onTrue onFalse : BlockId) (args : List Var)
deriving DecidableEq, Repr
```

The six-clause readings, all frozen by `#guard`/`rfl` receipts:

```text
successors  performCatch _ _ t _ e _ → [t, e]      branch _ _ t f _ → [t, f]
args        performCatch _ _ _ a _ _ → a           branch _ _ _ _ a → a
argsAt      performCatch _ _ _ a _ e, i → if i = 1 then e else a
            every other terminator, _              → args
arity       performCatch _ _ _ a _ _ → a.length+1  branch _ _ _ _ a → a.length
arityAt     performCatch _ _ _ a _ e, i → if i = 1 then e.length+1 else a.length+1
            every other terminator, _              → arity
operands    performCatch _ r _ a _ e → r :: (a ++ e)   branch t _ _ _ a → t :: a
isChoose    performCatch → false                   branch → true
decision?   performCatch → none                    branch _ s _ _ _ → some s
operation?  performCatch op _ _ _ _ _ → some op     branch → none
request?    performCatch _ r _ _ _ _ → some r       branch → none
```

with the four edge laws

```lean
theorem RawTerm.argsAt_zero (term : RawTerm) : term.argsAt 0 = term.args
theorem RawTerm.arityAt_zero (term : RawTerm) : term.arityAt 0 = term.arity
theorem RawTerm.argsAt_of_ne_one {term : RawTerm} {edge : Nat} (ne : edge ≠ 1) :
    term.argsAt edge = term.args
theorem RawTerm.arityAt_of_ne_one {term : RawTerm} {edge : Nat} (ne : edge ≠ 1) :
    term.arityAt edge = term.arity
```

`RawBlock`, `RawFlow`, `lookupBlock`, `Edge`, `ReachableFrom`, `Reachable`,
`EntryReachable` are unchanged.

### D3 — the eight clauses, with the edge clauses re-keyed (`Effects/Flow/Raw.lean`)

`AlphabetWF`, `IdsWF`, `RootsWF`, `ReferencesWF`, `OperationsWF`, `EntryWF`
and `CyclesWF` are the v2 propositions verbatim; each extends to the two new
terminators through `successors`, `decision?`, `operation?` and `isChoose`.
`TermsWF` becomes five-fold (frozen by `Iff.rfl`):

```lean
def ArityWF (raw : RawFlow Ty) (block : RawBlock Ty) : Prop :=
  ∀ (edge : Nat) (target : BlockId), block.term.successors[edge]? = some target →
    match lookupBlock raw target with
    | none => True
    | some targetBlock => targetBlock.params.length = block.term.arityAt edge

def ArgumentsWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) (block : RawBlock Ty) : Prop :=
  ∀ (edge : Nat) (target : BlockId), block.term.successors[edge]? = some target →
    ∀ slot, slot ∈ List.range (block.term.arityAt edge) →
      SlotWF alphabet raw block edge target slot

def BranchTestWF (alphabet : FlowAlphabet Ty) (block : RawBlock Ty) : Prop :=
  match block.term with
  | .branch test _ _ _ _ =>
      match block.params[test.index]? with
      | some actual => actual = alphabet.boolTy
      | none => True
  | _ => True

def TermsWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop :=
  (∀ block, block ∈ raw.blocks → block.VarsWF) ∧
  (∀ block, block ∈ raw.blocks → ArityWF raw block) ∧
  (∀ block, block ∈ raw.blocks → ArgumentsWF alphabet raw block) ∧
  (∀ block, block ∈ raw.blocks → OperandsWF alphabet raw block) ∧
  (∀ block, block ∈ raw.blocks → BranchTestWF alphabet block)
```

`SlotWF` gains its `performCatch` arm: on edge `1`, slot `errorArgs.length`
of the failure target is compared against `alphabet.errorTy`; off edge `1`,
slot `args.length` of the value target against `alphabet.answerTy`.
`OperandsWF` gains a `performCatch` arm identical to its `perform` arm (the
request carries `requestTy`). `FlowWF` keeps its eight fields.

### D4 — eighteen ordered clauses (`Effects/Flow/Admission.lean`)

`AdmissionClause` has exactly eighteen constructors in this order, and `scan`
lists them in this order (frozen by a `rfl` receipt, and `scan.length == 18`
by `#guard`):

```text
alphabetMismatch        entryTypeMismatch
duplicateBlockId        termTypeMismatch
duplicateDecisionId     branchTestType        ← the one v3 adds
nonCanonicalBlockOrder  unknownVariable
emptyRoots              argumentArity
duplicateRoot           argumentTypeMismatch
nonCanonicalRootOrder   unchosenCycle
entryNotRoot
danglingRoot
danglingSuccessor
unknownOperation
```

`branchTestType` sits immediately after `termTypeMismatch`, the other operand
clause, and before `unknownVariable`. `CheckSite` and `DiagnosticPayload` are
unchanged; the `argument` site's `successor` field is a position in
`RawTerm.successors`, so for a `performCatch` `.argument b 1 i` names the
failure edge and index `errorArgs.length` is the error slot.

Witness relations, frozen by ascription:

```lean
inductive TermFailureValid … : DiagnosticPayload Ty → Prop where
  | retTypeMismatch …                    -- v2
  | performRequestTypeMismatch …         -- v2
  | performCatchRequestTypeMismatch {operation request target args onError errorArgs
      operationDef actual}
      (term : block.term = .performCatch operation request target args onError errorArgs)
      (known : alphabet.lookup operation = some operationDef)
      (typed : block.params[request.index]? = some actual)
      (mismatch : actual ≠ alphabet.requestTy operationDef) :
      TermFailureValid alphabet raw block
        (.typeMismatch (alphabet.requestTy operationDef) actual)

inductive BranchFailureValid (alphabet : FlowAlphabet Ty) (block : RawBlock Ty) :
    DiagnosticPayload Ty → Prop where
  | testTypeMismatch {test site onTrue onFalse args actual}
      (term : block.term = .branch test site onTrue onFalse args)
      (typed : block.params[test.index]? = some actual)
      (mismatch : actual ≠ alphabet.boolTy) :
      BranchFailureValid alphabet block (.typeMismatch alphabet.boolTy actual)

inductive ArgumentFailureValid (alphabet) (raw) (block) (edge : Nat) (target : BlockId) :
    Nat → DiagnosticPayload Ty → Prop where
  | argument …      -- v2, over `(block.term.argsAt edge)[position]?`
  | answer …        -- v2, the plain `perform` answer slot
  | catchAnswer …   -- edge ≠ 1: slot args.length against `answerTy`
  | catchError …    -- edge = 1: slot errorArgs.length against `errorTy`
```

`Diagnostic.Valid` keeps every v2 constructor and gains `branchTestType`
(first failing block in table order, site `.term block.id`, payload the
`BranchFailureValid` payload). Its `argumentArity` and `argumentTypeMismatch`
constructors are re-stated over the edge index: the inner `FirstFailureAt`
now binds the successor's position and compares against
`candidate.term.arityAt edgeIndex`, and the reported payload of
`argumentArity` is `.arity (block.term.arityAt successorIndex) declared`.

### D5 — admission (retained shapes)

`diagnoseAt`, `FirstDiagnostic`, `CheckedFlow` (private `mk`; public `raw`,
`wf`, `erase`, `erase_eq_raw`, `ext`) and `admit` keep their v2 types
exactly. The checked constructor remains private.

## ENSURES

Proved without `sorry`, custom axioms, `partial`, `unsafe`, or
`Classical.choice`, within `propext` / `Quot.sound`. Every v2 statement is
retained verbatim and re-proved over the wider carrier:

1. `FlowWF.reachable_declared`
2. `cyclesChoose_iff` — now counting `branch` as a decision
3. `admit_sound`
4. `admit_complete` — relative to the frozen eight clauses
5. `error_iff_not_wf`
6. `error_iff_firstDiagnostic`
7. `admit_error_valid`
8. `diagnoseAt_some_valid`
9. `FirstDiagnostic.valid`, `FirstDiagnostic.condemns`
10. `Diagnostic.clause_all_complete` — now over eight fields and **eighteen**
    clauses
11. `erase_wf`, `erase_admit`, `admit_erase`, `CheckedFlow.erase_eq_raw`,
    `CheckedFlow.ext`

New in v3, frozen by `rfl` receipts rather than by name: the four edge laws
of D2 (`argsAt_zero`, `arityAt_zero`, `argsAt_of_ne_one`,
`arityAt_of_ne_one`), which are what makes "every v2 shape reads as it did" a
theorem and not a convention.

## Counterexample obligations

| ID | Frozen attack | Witness | Forced repair |
| --- | --- | --- | --- |
| `EF-FLOW-CE-007` | a caught failure unwinds regions, so the failure successor may sit outside the enclosing region | `EffectsTest/Counterexamples/Flow/FlowV3.lean`: `caughtInside` (both successors of the `performCatch` labelled with region 1) admits; `caughtOutside`, which moves the failure successor out of region 1, is refused with `⟨.successorLabel, some ⟨1⟩, some ⟨1⟩⟩` | the failure edge is a declared successor like any other, so `successorLabel` (v0.5.0) requires it to carry the block's own label; a caught failure continues *inside* the still-open region |
| `EF-FLOW-CE-008` | a `branch` is a value test and not a question for the tape, so a loop closed by a `branch` needs no decision entry | `FlowV3.lean`: `branchLoop` admits and `cyclesChoose branchLoop = true`; the same graph with the branch replaced by a `jump` (`jumpLoop`) is refused with `⟨.unchosenCycle, .block 0, .block ⟨0⟩⟩`; `branchOnNat` is refused with `⟨.branchTestType, .term ⟨1⟩, .typeMismatch .bool .nat⟩` | `isChoose` is true for `branch` and `decision?` names its site, so `CyclesWF` counts it and the tape bound survives; the test carries `boolTy`, enforced by `branchTestType` |

The battery's own executable receipts pin the clause each new shape is
refused by: `wrongErrorSlot` (`argumentTypeMismatch` at `.argument ⟨2⟩ 1 1`,
`.typeMismatch .str .nat` — the error slot is typed by `errorTy`),
`wrongErrorArity` (`argumentArity` at `.successor ⟨2⟩ 1`, `.arity 2 1` — the
failure edge has its own arity), `wrongAnswerSlot` (`argumentTypeMismatch` at
`.argument ⟨2⟩ 0 0` — the value edge keeps `answerTy`), `unknownCatch`
(`unknownOperation`), and `collidingSites` (`duplicateDecisionId` at a
`branch` repeating a `choose`'s site).

## Supersession of v2 rows

- `EF-FLOW-CE-001..003` are retained with their sites and their witnesses.
  `EF-FLOW-CE-003`'s receipt reads the value edge, which `argsAt 0` and
  `arityAt 0` leave unchanged.
- The v2 packet's D2 terminator list and its `TermsWF` clauses 2–3 are
  superseded by D2 and D3 above. Its `ArgumentFailureValid` is superseded by
  the four-arm, edge-indexed relation of D4, and its seventeen-clause `scan`
  by the eighteen-clause `scan`.

## Decrease, frame, and trust

Unchanged from v2. Every clause check recurses over finite lists; the edge
clauses now recurse over `successors` with the position in hand, which is the
same list. The cycle checker is structurally recursive on fuel bounded by the
block table. The checker mutates no state, invokes no handler, and runs no
host code; its frame is the alphabet and the raw value. The proof ceiling is
`[propext, Quot.sound]`, and the default gate rejects custom axioms, `sorry`,
`partial`, `unsafe`, and unrooted modules.

## Acceptance commands

```text
lake env lean EffectsTest/Flow/FlowV3Contract.lean
lake env lean EffectsTest/Counterexamples/Flow/FlowV3.lean
lake build                                # default targets, runs #effects_axiom_gate
```
