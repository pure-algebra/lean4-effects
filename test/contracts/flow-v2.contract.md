# Flow v2 contract packet

Status: **SUPERSEDED by `test/contracts/flow-v3.contract.md` (Effects v0.7.0).**
Originally FROZEN / RED, breaker-authored 2026-09-02; landed green at v0.4.0.

This packet is retained as the record of the v2 freeze. Where it and the v3
packet disagree, **v3 is the live text**: the terminator list (D2), the two
edge clauses of D3, the `ArgumentFailureValid` relation, and the clause count
and `scan` order of D4 all moved in v3, and v3 owns the executable `scan` pin
(`EffectsTest/Flow/FlowV3Contract.lean`, `rfl` on the eighteen-clause list
plus `#guard scan.length == 18`). The counts below — "seventeen ordered
admission clauses", "the thirteen v1 clauses" — were true of v2 and are false
of the tree; they are left in place because a superseded packet is a record,
not a specification. Every other frozen declaration of this packet stands, and
its counterexample rows `EF-FLOW-CE-001..003` are retained with their sites.

Implementation fence: `Effects/Flow/{Block,Raw,Admission,Checked}.lean`

Battery: `EffectsTest/Flow/FlowV2Contract.lean` (kernel receipts: ascriptions,
`rfl`, `decide`, hand proofs)

Axiom report: `EffectsTest/Flow/FlowV2AxiomReport.lean`

Counterexamples: `test/counterexamples/REGISTER.md`, rows `EF-FLOW-CE-001`
through `EF-FLOW-CE-003`; witnesses and the packet's executable admission
receipts in `EffectsTest/Counterexamples/Flow/FlowV2.lean`; attack shapes in
`test/counterexamples/flow/ATTACKS.md`

Version: this packet is Effects v0.4.0. The v1 admission packets of
lean4-effect4 (`test/contracts/flow-admission.contract.md`,
`test/contracts/flow-diagnostic-precision.contract.md`, batteries
`Effect4Test/Flow/{AdmissionContract,DiagnosticPrecisionContract,PrivacyContract,AxiomReport}.lean`
at lean4-effect4 `c951711`) are superseded by this packet. Their retained
attacks move here as `EffectsTest/Flow/*` with the packet; two of their rows
flip (see "Supersession of v1 rows").

## Claim boundary

Flow v1 (`Effects/Flow/*` at v0.3.1) gives every block one payload, and
`perform` replaces that payload with the operation's answer. A block cannot
hold both an earlier value and the answer, so `let x ← get; put x; return x`
has no first-order spelling. Flow v2 gives every block a parameter list
(SSA-style block arguments, as in js_of_ocaml's block IR): a terminator names
its operands by position in the current block's parameters, `jump` and
`choose` pass an argument list, and `perform` passes an argument list plus the
answer. Flow v2 also adds one decidable global clause: every cycle of the
successor graph passes through a block whose terminator is `choose`, so a
finite decision tape bounds every run.

This packet freezes the carrier, the eight well-formedness clauses, the
seventeen ordered admission clauses with exact witnesses, the decidable cycle
checker with its soundness-and-completeness law, and the retained admission
theorems over the new carrier.

Not claimed:

- **No execution semantics.** The packet defines no run, no decision tape,
  no evaluator, and no theorem of the form "a tape of length `n` bounds a
  run". `CyclesWF` is a syntactic invariant of the declared graph; the
  run-bounding consequence is a later packet's theorem over this carrier.
- **No regions and no resources.** Region entry, exit, finalizers, and
  resource scoping are not terminators here and are not encoded in
  parameters. They are a later packet.
- **No pure atoms.** There is no terminator for a pure computation. A pure
  step is an ordinary operation of the alphabet (`succ : nat → nat` is an
  operation, not a terminator form); the `incr` receipt therefore performs
  `get` then `put` with the answer as the request and returns the entry
  parameter.
- **No elaboration to `Program`,** no handlers, no host correspondence, no
  TypeScript.
- **No reachability coverage.** Unreachable declared blocks remain admitted;
  every clause, including `CyclesWF`, is checked over the whole declared
  document.

## Design basis

- The successor graph (`Edge`, `ReachableFrom`) is unchanged: a terminator's
  successors are its block targets in source order, `[left, right]` for
  `choose`.
- A `Var` is a position in the current block's parameter list; it is not a
  name, has no scope beyond its block, and is typed by `params[index]`.
- A `choose` block is the only place a run may branch; every cycle must
  contain one so that a finite tape of decisions bounds every run.
- Diagnostics keep the v1 discipline: a fixed clause order, an exact site, a
  typed payload, and a `Diagnostic.Valid` witness that the reported clause
  condemns the input at its first source occurrence.
- Payload orientation (frozen): a target block's parameter list is always the
  `actual` side; the `expected` side is what flows into it — the sender's
  argument types, the operation's answer type, or for the entry the flow's
  `inputTy`. For an operand (`ret` value, `perform` request) `expected` is
  the flow's `resultTy` or the operation's `requestTy` and `actual` is the
  operand's type. Counts follow the same rule: `.arity expected actual` has
  `expected` = the count supplied to the target (`RawTerm.arity`, or `1` at
  the entry) and `actual` = the target's declared count.

## REQUIRES

1. Lean core and Std at the repository's pinned Lean 4.33.1 toolchain; no
   third-party Lake dependency.
2. `Ty` has decidable equality at the admission boundary (`[DecidableEq Ty]`
   on `admit`, `diagnoseAt`, `FirstDiagnostic`, and the admission theorems,
   as today). `FlowAlphabet` keeps its executable lookup and two inverse
   laws. Universes are as today: `FlowAlphabet.{uTy, uOp}`, `CheckedFlow`
   in `Type uTy`.
3. `cyclesChoose` needs no `DecidableEq Ty`; it inspects only identities and
   terminators.
4. `cyclesChoose` is kernel-computable: it is defined by structural
   recursion (fuel or list recursion, no well-founded recursion, no
   `Decidable` instances built by `simp`), so that `decide` closes
   `cyclesChoose raw = true` on a concrete flow and consumers obtain
   `CyclesWF raw` for concrete flows through `cyclesChoose_iff`. The
   battery's `by decide` receipts enforce this.

## Frozen declarations

Binder names may differ. Names, universes, argument roles, constructor
fields, result types, and theorem propositions are frozen by the battery's
ascriptions; the receipts marked `rfl`/`Iff.rfl` freeze the stated bodies
definitionally.

### D0 — identifiers and variables (`Effects/Flow/Block.lean`)

`BlockId`, `OperationId`, `AlphabetId`, `DecisionId` are retained. New:

```lean
/-- A position in the current block's parameter list. -/
structure Var where
  index : Nat
deriving DecidableEq, Repr
```

### D1 — closed alphabet

`FlowAlphabet.{uTy, uOp} Ty` is retained unchanged (id, `Op`, `operationId`,
`lookup`, `requestTy`, `answerTy`, `lookup_operationId`,
`operationId_of_lookup`).

### D2 — terms and blocks

```lean
inductive RawTerm where
  | ret (value : Var)
  | jump (target : BlockId) (args : List Var)
  | perform (operation : OperationId) (request : Var) (target : BlockId) (args : List Var)
      -- the target receives args ++ [answer]
  | choose (decision : DecisionId) (left right : BlockId) (args : List Var)
      -- both targets receive args
deriving DecidableEq, Repr

def RawTerm.successors : RawTerm → List BlockId
  -- ret → [];  jump t _ → [t];  perform _ _ t _ → [t];  choose _ l r _ → [l, r]
def RawTerm.args : RawTerm → List Var
  -- ret → [];  jump _ a → a;  perform _ _ _ a → a;  choose _ _ _ a → a
def RawTerm.operands : RawTerm → List Var
  -- every variable occurrence in source order:
  -- ret v → [v];  jump _ a → a;  perform _ r _ a → r :: a;  choose _ _ _ a → a
def RawTerm.arity : RawTerm → Nat
  -- the number of values every successor receives:
  -- ret → 0;  jump _ a → a.length;  perform _ _ _ a → a.length + 1;  choose _ _ _ a → a.length
def RawTerm.isChoose : RawTerm → Bool
  -- choose → true;  otherwise false
def RawTerm.decision? : RawTerm → Option DecisionId
  -- choose d _ _ _ → some d;  otherwise none

structure RawBlock (Ty : Type uTy) where
  id : BlockId
  params : List Ty
  term : RawTerm
deriving DecidableEq, Repr
```

`RawFlow Ty` (alphabet, roots, entry, inputTy, resultTy, blocks) is retained
unchanged. `args`, `operands`, `arity`, `isChoose`, and `decision?` are frozen by `rfl`
receipts on each constructor; `successors` keeps its v1 type and meaning and
is pinned executably in the counterexample module.

### D3 — lookup, reachability, well-formedness (`Effects/Flow/Raw.lean`)

Retained unchanged: `lookupBlock`, `Edge`, `ReachableFrom`, `Reachable`,
`EntryReachable`, `AlphabetWF`, `IdsWF`, `RootsWF`, `ReferencesWF`,
`OperationsWF` (the `perform` pattern is now four-ary). Their meanings are
those of the v1 contract.

Strengthened:

- `EntryWF raw`: the entry resolves and its parameter list is exactly
  `[raw.inputTy]`.
- `TermsWF alphabet raw`: for every declared block `b` with parameters `ps`
  (reachable or not), the conjunction of the four term clauses below:
  1. *variables* — every `v ∈ RawTerm.operands b.term` has
     `v.index < ps.length`;
  2. *arity* — every successor `t` of `b` that resolves to `tb` has
     `tb.params.length = RawTerm.arity b.term`;
  3. *argument types* — for every successor `t` resolving to `tb`, every
     position `i` with `(RawTerm.args b.term)[i]? = some v`,
     `ps[v.index]? = some s`, and `tb.params[i]? = some d` has `s = d`; and
     for `b.term = .perform op _ t args` with `alphabet.lookup op = some o`
     and `tb.params[args.length]? = some d`, `alphabet.answerTy o = d`;
  4. *operand types* — for `b.term = .ret v` with `ps[v.index]? = some a`,
     `a = raw.resultTy`; for `b.term = .perform op r _ _` with
     `alphabet.lookup op = some o` and `ps[r.index]? = some a`,
     `a = alphabet.requestTy o`.

  Clauses 2–4 are guarded by resolution and operation closure, which
  `ReferencesWF` and `OperationsWF` own, and clauses 3–4 are guarded by
  variable range and arity, which clauses 1–2 own. Together with
  `ReferencesWF` and `OperationsWF`, `TermsWF` therefore says: every operand
  is in range; `ret v` returns `resultTy`; every successor resolves to a
  block whose parameter list equals the supplied list (`argTys` for `jump`
  and `choose`, `argTys ++ [answerTy op]` for `perform`, with
  `argTys[i] = ps[args[i].index]`); and a `perform` request has type
  `requestTy op`.

New (frozen by `Iff.rfl` receipts):

```lean
/-- A declared edge whose source block is not a `choose`. -/
def EdgeNoChoose (raw : RawFlow Ty) (source target : BlockId) : Prop :=
  ∃ block, block ∈ raw.blocks ∧ block.id = source ∧
    block.term.isChoose = false ∧ target ∈ block.term.successors

/-- Reflexive-transitive closure of `EdgeNoChoose`. -/
inductive ReachableNoChoose (raw : RawFlow Ty) : BlockId → BlockId → Prop where
  | refl (source : BlockId) : ReachableNoChoose raw source source
  | step {source middle target : BlockId} :
      ReachableNoChoose raw source middle →
      EdgeNoChoose raw middle target →
      ReachableNoChoose raw source target

/-- Every cycle of the successor graph passes through a `choose` block. -/
def CyclesWF (raw : RawFlow Ty) : Prop :=
  ∀ source target, EdgeNoChoose raw source target →
    ReachableNoChoose raw target source → False

structure FlowWF (alphabetDef : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop where
  alphabet : AlphabetWF alphabetDef raw
  ids : IdsWF raw
  roots : RootsWF raw
  references : ReferencesWF raw
  operations : OperationsWF alphabetDef raw
  entry : EntryWF raw
  terms : TermsWF alphabetDef raw
  cycles : CyclesWF raw

/-- Decidable checker for `CyclesWF`; needs no `DecidableEq Ty`. -/
def cyclesChoose (raw : RawFlow Ty) : Bool
theorem cyclesChoose_iff {raw : RawFlow Ty} :
    cyclesChoose raw = true ↔ CyclesWF raw
```

A `jump` or `perform` self-loop violates `CyclesWF` (`EdgeNoChoose a a` with
`ReachableNoChoose.refl a`); a `choose` self-loop satisfies it. Like every
other clause, `CyclesWF` is whole-document: an unreachable unchosen cycle is
rejected. `cyclesChoose` may live in `Raw.lean` or `Admission.lean`.

### D4 — ordered diagnostics (`Effects/Flow/Admission.lean`)

`AdmissionClause` has exactly seventeen constructors in this order, and
`scan` lists them in this order (frozen by a `rfl` receipt):

```text
alphabetMismatch
duplicateBlockId
duplicateDecisionId
nonCanonicalBlockOrder
emptyRoots
duplicateRoot
nonCanonicalRootOrder
entryNotRoot
danglingRoot
danglingSuccessor
unknownOperation
entryTypeMismatch
termTypeMismatch
unknownVariable
argumentArity
argumentTypeMismatch
unchosenCycle
```

```lean
inductive CheckSite where
  | flow
  | block (index : Nat)
  | decision (block : BlockId)
  | root (index : Nat)
  | successor (block : BlockId) (index : Nat)
  | operation (block : BlockId)
  | entry
  | term (block : BlockId)
  | argument (block : BlockId) (successor index : Nat)
      -- position `index` of the value list flowing along successor edge
      -- `successor` (a position in `RawTerm.successors`) of `block`;
      -- for `perform`, index `args.length` is the answer slot

inductive DiagnosticPayload (Ty : Type uTy) where
  | none
  | alphabet (expected actual : AlphabetId)
  | block (id : BlockId)
  | decision (id : DecisionId)
  | operation (id : OperationId)
  | typeMismatch (expected actual : Ty)
  | variable (v : Var)
  | arity (expected actual : Nat)
```

`argument` carries three fields rather than the two of the design sketch:
a `choose` delivers one argument list to two receivers, and a site that
names the block and the position but not the receiver cannot say which
receiver's parameter was compared. `Diagnostic Ty` (`clause`, `site`,
`payload`) and `FirstFailureAt` are retained unchanged.

Clause-local witness relations:

```lean
/-- Operand typing failures of one block (clause `termTypeMismatch`), guarded
by variable range and operation closure. -/
inductive TermFailureValid (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) : DiagnosticPayload Ty → Prop where
  | retTypeMismatch {value : Var} {actual : Ty}
      (term : block.term = .ret value)
      (typed : block.params[value.index]? = some actual)
      (mismatch : actual ≠ raw.resultTy) :
      TermFailureValid alphabet raw block (.typeMismatch raw.resultTy actual)
  | performRequestTypeMismatch {operation : OperationId} {request : Var}
      {target : BlockId} {args : List Var} {operationDef : alphabet.Op} {actual : Ty}
      (term : block.term = .perform operation request target args)
      (known : alphabet.lookup operation = some operationDef)
      (typed : block.params[request.index]? = some actual)
      (mismatch : actual ≠ alphabet.requestTy operationDef) :
      TermFailureValid alphabet raw block
        (.typeMismatch (alphabet.requestTy operationDef) actual)

/-- Positional typing failures on one successor edge of one block (clause
`argumentTypeMismatch`), guarded by resolution, arity, variable range, and
operation closure. -/
inductive ArgumentFailureValid (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) (target : BlockId) : Nat → DiagnosticPayload Ty → Prop where
  | argument {targetBlock : RawBlock Ty} {position : Nat} {argument : Var}
      {supplied declared : Ty}
      (found : lookupBlock raw target = some targetBlock)
      (argumentAt : block.term.args[position]? = some argument)
      (suppliedAt : block.params[argument.index]? = some supplied)
      (declaredAt : targetBlock.params[position]? = some declared)
      (mismatch : supplied ≠ declared) :
      ArgumentFailureValid alphabet raw block target position
        (.typeMismatch supplied declared)
  | answer {operation : OperationId} {request : Var} {args : List Var}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty} {declared : Ty}
      (term : block.term = .perform operation request target args)
      (known : alphabet.lookup operation = some operationDef)
      (found : lookupBlock raw target = some targetBlock)
      (declaredAt : targetBlock.params[args.length]? = some declared)
      (mismatch : alphabet.answerTy operationDef ≠ declared) :
      ArgumentFailureValid alphabet raw block target args.length
        (.typeMismatch (alphabet.answerTy operationDef) declared)
```

The eleven v1 constructors of `TermFailureValid` (`jumpMissing`,
`jumpTypeMismatch`, `performMissingTarget`, `performAnswerTypeMismatch`, the
four `choose` forms, and the v1 `retTypeMismatch` /
`performRequestTypeMismatch` over `inputTy`) are replaced: edge typing is
owned by `argumentArity` and `argumentTypeMismatch`, and a missing target or
unknown operation is owned by `danglingSuccessor` and `unknownOperation`,
never re-reported by a term clause.

`Diagnostic.Valid alphabet raw : Diagnostic Ty → Prop` keeps the v1
constructors `alphabetMismatch`, `duplicateBlockId`, `duplicateDecisionId`,
`nonCanonicalBlockOrder`, `emptyRoots`, `duplicateRoot`,
`nonCanonicalRootOrder`, `entryNotRoot`, `danglingRoot`,
`danglingSuccessor`, `unknownOperation`, `entryMissing`, and
`termTypeMismatch` with their v1 statements (patterns four-ary;
`duplicateDecisionId` scans prior decisions through `RawTerm.decision?`),
replaces `entryTypeMismatch`, and gains five:

```lean
  | entryArity {block : RawBlock Ty}
      (found : lookupBlock raw raw.entry = some block)
      (arity : block.params.length ≠ 1) :
      Valid alphabet raw ⟨.entryTypeMismatch, .entry, .arity 1 block.params.length⟩
  | entryTypeMismatch {block : RawBlock Ty} {actual : Ty}
      (found : lookupBlock raw raw.entry = some block)
      (single : block.params = [actual])
      (mismatch : actual ≠ raw.inputTy) :
      Valid alphabet raw ⟨.entryTypeMismatch, .entry, .typeMismatch raw.inputTy actual⟩
  | unknownVariable {blockIndex operandIndex : Nat} {block : RawBlock Ty} {unknown : Var}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate witness =>
          FirstFailureAt candidate.term.operands
            (fun _ operand reported =>
              reported = operand ∧ candidate.params.length ≤ operand.index)
            witness.1 witness.2 witness.2)
        blockIndex block (operandIndex, unknown)) :
      Valid alphabet raw ⟨.unknownVariable, .term block.id, .variable unknown⟩
  | argumentArity {blockIndex successorIndex : Nat} {block : RawBlock Ty}
      {target : BlockId} {declared : Nat}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate witness =>
          FirstFailureAt candidate.term.successors
            (fun _ successor reported =>
              ∃ targetBlock : RawBlock Ty,
                lookupBlock raw successor = some targetBlock ∧
                targetBlock.params.length = reported ∧
                reported ≠ candidate.term.arity)
            witness.1 witness.2.1 witness.2.2)
        blockIndex block (successorIndex, target, declared)) :
      Valid alphabet raw
        ⟨.argumentArity, .successor block.id successorIndex, .arity block.term.arity declared⟩
  | argumentTypeMismatch {blockIndex successorIndex position : Nat}
      {block : RawBlock Ty} {target : BlockId} {payload : DiagnosticPayload Ty}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate witness =>
          FirstFailureAt candidate.term.successors
            (fun _ successor edge =>
              FirstFailureAt (List.range candidate.term.arity)
                (fun _ slot failure =>
                  ArgumentFailureValid alphabet raw candidate successor slot failure)
                edge.1 edge.1 edge.2)
            witness.1 witness.2.1 witness.2.2)
        blockIndex block (successorIndex, target, (position, payload))) :
      Valid alphabet raw
        ⟨.argumentTypeMismatch, .argument block.id successorIndex position, payload⟩
  | unchosenCycle {index : Nat} {block : RawBlock Ty}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate reported =>
          reported = candidate.id ∧
          ∃ next : BlockId,
            EdgeNoChoose raw candidate.id next ∧ ReachableNoChoose raw next candidate.id)
        index block block.id) :
      Valid alphabet raw ⟨.unchosenCycle, .block index, .block block.id⟩
```

Source order is the v1 discipline extended: blocks in table order; within a
block, operands in `RawTerm.operands` order, successors in
`RawTerm.successors` order (left before right), and positions ascending
within a successor. The condemned block of `unchosenCycle` is the first
declared block that lies on a cycle avoiding `choose` blocks.

### D5 — admission (retained shapes over the new carrier)

`diagnoseAt`, `FirstDiagnostic` (`condemns`, `prior`), `CheckedFlow` (private
`mk`, public `raw`, `wf`, `erase`, `erase_eq_raw`, `ext`), and `admit` keep
their v1 types exactly. The checked constructor remains private
(`E4-FLOW-CE-015` receipt retained in the battery).

## ENSURES

Proved without `sorry`, custom axioms, `partial`, `unsafe`, or
`Classical.choice`, within `propext`/`Quot.sound`; statements are the v1
statements over the new carrier, ascribed in the battery:

1. `FlowWF.reachable_declared`: `FlowWF alphabet raw → Reachable raw target →
   ∃ block, lookupBlock raw target = some block`.
2. `cyclesChoose_iff`: `cyclesChoose raw = true ↔ CyclesWF raw` (new).
3. `admit_sound`: `admit alphabet raw = .ok checked → FlowWF alphabet raw`.
4. `admit_complete`: `FlowWF alphabet raw → ∃ checked, admit alphabet raw = .ok checked`.
5. `error_iff_not_wf`: `(∃ diagnostic, admit alphabet raw = .error diagnostic) ↔ ¬ FlowWF alphabet raw`.
6. `error_iff_firstDiagnostic`: `admit alphabet raw = .error diagnostic ↔ FirstDiagnostic alphabet raw diagnostic`.
7. `admit_error_valid`: `admit alphabet raw = .error diagnostic → Diagnostic.Valid alphabet raw diagnostic`.
8. `diagnoseAt_some_valid`: `diagnoseAt alphabet raw clause = some diagnostic → Diagnostic.Valid alphabet raw diagnostic`.
9. `FirstDiagnostic.valid`, `FirstDiagnostic.condemns` (projection).
10. `Diagnostic.clause_all_complete`: `FlowWF alphabet raw ↔ ∀ clause ∈ scan, diagnoseAt alphabet raw clause = none` — now over eight fields and seventeen clauses.
11. `erase_wf`, `erase_admit`, `admit_erase`, `CheckedFlow.erase_eq_raw`, `CheckedFlow.ext`.

`admit_complete` is relative to the frozen eight clauses. The receipts
`example : CyclesWF incr := cyclesChoose_iff.mp (by decide)` and the
`¬ CyclesWF` hand proofs are kernel-checked consequences of 2.

## Counterexample obligations

| ID | Frozen attack | Witness | Forced repair |
| --- | --- | --- | --- |
| `EF-FLOW-CE-001` | one payload can carry the environment | v0.3.1 `perform (operation) (target)`: the target's single input is the answer (design row); v2 `incr` admits and returns the entry parameter after two performs | block parameters; `perform` target receives `args ++ [answer]` |
| `EF-FLOW-CE-002` | a tape bounds every run without a cycle clause | v0.3.1 `admit` accepts a `jump` self-loop (transcript in `ATTACKS.md`, lean4-effect4 `E4-FLOW-CE-005`); v2 rejects it with `unchosenCycle` at `.block 0` and admits the `choose` self-loop | `CyclesWF` / `unchosenCycle`, `cyclesChoose_iff` |
| `EF-FLOW-CE-003` | argument arity can be checked without types | right arity, wrong type: `diagnoseAt … .argumentArity = none`, `admit` fails with `argumentTypeMismatch` at `.argument b 0 0` | `argumentTypeMismatch` is a separate positional clause after `argumentArity` |

## Supersession of v1 rows

- `E4-FLOW-CE-005` ("a locally typed self-cycle is admitted; acyclicity is
  not a hidden clause") and the cycle half of `E4-FLOW-CE-014` ("an
  unreachable closed self-cycle is admitted") are reversed by this packet:
  an unchosen cycle, reachable or not, is rejected by `unchosenCycle`. The
  dangling half of `E4-FLOW-CE-014` (whole-document closure) stands.
- `E4-FLOW-CE-004` (answer type versus target input) becomes an
  `argumentTypeMismatch` at the answer slot `.argument b 0 args.length`, no
  longer a `termTypeMismatch`.
- `E4-FLOW-CE-001/002/003/007/013/015/016` are retained with their sites.

## Decrease, frame, and trust

Every clause check recurses over finite lists; the cycle checker is
structurally recursive on fuel bounded by the block table (REQUIRES 4).
Reachability relations are inductive, never executed. The checker mutates no
state, invokes no handler, and runs no host code; its frame is the alphabet
and the raw value. The proof ceiling is `[propext, Quot.sound]`; the default
gate rejects custom axioms, `sorry`, `partial`, `unsafe`, and unrooted
modules.

## RED and acceptance commands

Red state, recorded by the breaker:

```text
lake build Effects                                                   # green: Effects/ untouched
lake env lean -DmaxErrors=10000 EffectsTest/Flow/FlowV2Contract.lean # fails
```

The battery must fail only with unknown identifier / unknown constant
diagnostics for the frozen v2 names; no parse error, no type mismatch, no
arity error. This is achieved by carrying only kernel receipts whose
statements are headed by a frozen v2 name (a v2-shaped literal elaborates
only as an argument of such a head while the carrier is v0.3.1) and by
`set_option autoImplicit false`, without which a missing `Var` is silently
auto-bound. The executable admission receipts (`#guard` over `admit`) are in
`EffectsTest/Counterexamples/Flow/FlowV2.lean`; that module is red for the
same missing names plus the consequential arity and evaluation diagnostics
Lean attaches to `def` bodies and `#guard` lines, and no purity claim is made
for it. All three modules are listed in
`test/fixtures/trust-gate/known-red.txt`, so `./scripts/test-trust-gate.sh`
excises them and passes on the remaining tree.

Green acceptance:

```text
lake env lean EffectsTest/Flow/FlowV2Contract.lean
lake env lean EffectsTest/Counterexamples/Flow/FlowV2.lean
lake build                                # default targets, runs #effects_axiom_gate
./scripts/test-trust-gate.sh              # after removing the three known-red entries
```

The builder removes the three `known-red.txt` entries the moment the modules
are green, records the axiom receipts of `EffectsTest/Flow/FlowV2AxiomReport.lean`,
and does not edit this contract, the battery, the axiom report, the
counterexample module, or the register rows. A builder may repair test
elaboration (a proof term, a `show`) without changing an attacked statement,
witness, or acceptance condition.
