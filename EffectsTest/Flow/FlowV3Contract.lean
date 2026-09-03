/-
Contract packet: `test/contracts/flow-v3.contract.md`

Battery for Flow v3 (Effects v0.7.0), which supersedes the terminator list and
the two edge clauses of `test/contracts/flow-v2.contract.md`. The retained v2
surface stays pinned in `EffectsTest/Flow/FlowV2Contract.lean`, re-spelled
where v3 changed it; this file pins only what v3 adds:

* the two terminators `performCatch` and `branch`, and the reading every
  projection gives them;
* the alphabet's two new rows, `errorTy` and `boolTy`;
* the successor-indexed `argsAt` / `arityAt`, and the `ArityWF`, `SlotWF` and
  `ArgumentsWF` clauses stated over them;
* the one new admission clause, `branchTestType`, its `BranchTestWF`
  proposition, its `BranchFailureValid` witness relation and its place in the
  eighteen-clause scan order;
* the two new arms of `ArgumentFailureValid`, which type a `performCatch`'s
  answer slot and its error slot apart.

Every receipt is kernel-checked: `#check` ascriptions, `rfl`, `decide`, and
`#guard` over `admit`. The two named attacks live in
`EffectsTest/Counterexamples/Flow/FlowV3.lean`.
-/

import Effects.Flow.Admission
import Effects.Flow.Block
import Effects.Flow.Checked
import Effects.Flow.Raw

set_option autoImplicit false

namespace EffectsTest.Flow.FlowV3Contract

open Effects

universe uTy uOp

section SurfaceSnapshot

/-! V0: the alphabet's two new rows. -/

#check (@FlowAlphabet.errorTy :
  ∀ {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty), alphabet.Op → Ty)

#check (@FlowAlphabet.boolTy :
  ∀ {Ty : Type uTy}, FlowAlphabet.{uTy, uOp} Ty → Ty)

/-! V1: the two terminators. -/

#check (@RawTerm.performCatch :
  OperationId → Var → BlockId → List Var → BlockId → List Var → RawTerm)

#check (@RawTerm.branch :
  Var → DecisionId → BlockId → BlockId → List Var → RawTerm)

/-! V2: the successor-indexed projections. -/

#check (@RawTerm.argsAt : RawTerm → Nat → List Var)
#check (@RawTerm.arityAt : RawTerm → Nat → Nat)
#check (@RawTerm.operation? : RawTerm → Option OperationId)
#check (@RawTerm.request? : RawTerm → Option Var)

end SurfaceSnapshot

section Projections

def blockId (value : Nat) : BlockId := ⟨value⟩
def operationId (value : Nat) : OperationId := ⟨value⟩
def decisionId (value : Nat) : DecisionId := ⟨value⟩

/-- The `performCatch` this section reads: `run` on `⟨0⟩`, value successor
block 2 with no carried arguments, failure successor block 3 carrying `⟨0⟩`. -/
def catcher : RawTerm :=
  .performCatch (operationId 1) ⟨0⟩ (blockId 2) [] (blockId 3) [⟨0⟩]

/-- The `branch` this section reads: test `⟨1⟩` at site 0, targets 4 and 5,
both carrying `⟨0⟩`. -/
def brancher : RawTerm :=
  .branch ⟨1⟩ (decisionId 0) (blockId 4) (blockId 5) [⟨0⟩]

/-! The value successor comes first, the failure successor second: the edge
index `1` *is* the failure edge, and that is what `argsAt` and `arityAt`
key on. -/

#guard RawTerm.successors catcher == [blockId 2, blockId 3]
#guard RawTerm.successors brancher == [blockId 4, blockId 5]

#guard RawTerm.args catcher == ([] : List Var)
#guard RawTerm.argsAt catcher 0 == ([] : List Var)
#guard RawTerm.argsAt catcher 1 == [(⟨0⟩ : Var)]
#guard RawTerm.args brancher == [(⟨0⟩ : Var)]
#guard RawTerm.argsAt brancher 0 == [(⟨0⟩ : Var)]
#guard RawTerm.argsAt brancher 1 == [(⟨0⟩ : Var)]

#guard RawTerm.arity catcher == 1
#guard RawTerm.arityAt catcher 0 == 1
#guard RawTerm.arityAt catcher 1 == 2
#guard RawTerm.arity brancher == 1
#guard RawTerm.arityAt brancher 0 == 1
#guard RawTerm.arityAt brancher 1 == 1

/-- A `performCatch` names its request before both argument lists; a `branch`
names its test before its arguments. -/
#guard RawTerm.operands catcher == [(⟨0⟩ : Var), ⟨0⟩]
#guard RawTerm.operands brancher == [(⟨1⟩ : Var), ⟨0⟩]

/-- A `performCatch` is not a decision; a `branch` is. -/
#guard RawTerm.isChoose catcher == false
#guard RawTerm.isChoose brancher == true
#guard RawTerm.decision? catcher == (none : Option DecisionId)
#guard RawTerm.decision? brancher == some (decisionId 0)

/-- Both perform an alphabet operation. -/
#guard RawTerm.operation? catcher == some (operationId 1)
#guard RawTerm.operation? brancher == (none : Option OperationId)
#guard RawTerm.request? catcher == some (⟨0⟩ : Var)

/-- Off the failure edge every terminator supplies its value list; `argsAt 0`
and `arityAt 0` are exactly `args` and `arity`. -/
example : RawTerm.argsAt catcher 0 = RawTerm.args catcher := RawTerm.argsAt_zero catcher
example : RawTerm.arityAt catcher 0 = RawTerm.arity catcher := RawTerm.arityAt_zero catcher
example : RawTerm.argsAt catcher 2 = RawTerm.args catcher :=
  RawTerm.argsAt_of_ne_one (by decide)
example : RawTerm.arityAt catcher 2 = RawTerm.arity catcher :=
  RawTerm.arityAt_of_ne_one (by decide)

end Projections

section Clauses

/-! V3: the edge clauses, keyed by the position of the edge in `successors`. -/

#check (@ArityWF : {Ty : Type uTy} → RawFlow Ty → RawBlock Ty → Prop)

#check (@SlotWF :
  {Ty : Type uTy} →
  FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → RawBlock Ty → Nat → BlockId → Nat → Prop)

#check (@ArgumentsWF :
  {Ty : Type uTy} →
  FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → RawBlock Ty → Prop)

/-- `ArityWF` quantifies over the edge index, not over the target: a
`performCatch`'s two successors are checked against different counts. -/
example {Ty : Type uTy} (raw : RawFlow Ty) (block : RawBlock Ty) :
    ArityWF raw block ↔
      ∀ (edge : Nat) (target : BlockId), block.term.successors[edge]? = some target →
        match lookupBlock raw target with
        | none => True
        | some targetBlock => targetBlock.params.length = block.term.arityAt edge :=
  Iff.rfl

example {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) :
    ArgumentsWF alphabet raw block ↔
      ∀ (edge : Nat) (target : BlockId), block.term.successors[edge]? = some target →
        ∀ slot, slot ∈ List.range (block.term.arityAt edge) →
          SlotWF alphabet raw block edge target slot :=
  Iff.rfl

/-! V4: the one new clause. -/

#check (@AdmissionClause.branchTestType : AdmissionClause)

#check (@BranchTestWF :
  {Ty : Type uTy} → FlowAlphabet.{uTy, uOp} Ty → RawBlock Ty → Prop)

example {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty) (block : RawBlock Ty) :
    BranchTestWF alphabet block ↔
      match block.term with
      | .branch test _ _ _ _ =>
          match block.params[test.index]? with
          | some actual => actual = alphabet.boolTy
          | none => True
      | _ => True :=
  Iff.rfl

#check (@BranchFailureValid :
  {Ty : Type uTy} →
  FlowAlphabet.{uTy, uOp} Ty → RawBlock Ty → DiagnosticPayload Ty → Prop)

#check (@BranchFailureValid.testTypeMismatch :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty} {block : RawBlock Ty}
      {test : Var} {site : DecisionId} {onTrue onFalse : BlockId}
      {args : List Var} {actual : Ty},
    block.term = .branch test site onTrue onFalse args →
    (RawBlock.params block)[test.index]? = some actual →
    actual ≠ alphabet.boolTy →
    BranchFailureValid alphabet block (.typeMismatch alphabet.boolTy actual))

#check (@Diagnostic.Valid.branchTestType :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty}
      {payload : DiagnosticPayload Ty},
    FirstFailureAt raw.blocks
      (fun _ candidate failure => BranchFailureValid alphabet candidate failure)
      index block payload →
    Diagnostic.Valid alphabet raw
      { clause := .branchTestType
        site := .term block.id
        payload := payload })

/-- Eighteen ordered clauses; `branchTestType` follows `termTypeMismatch`,
the other operand clause, and precedes `unknownVariable`. -/
example : scan = [
    .alphabetMismatch,
    .duplicateBlockId,
    .duplicateDecisionId,
    .nonCanonicalBlockOrder,
    .emptyRoots,
    .duplicateRoot,
    .nonCanonicalRootOrder,
    .entryNotRoot,
    .danglingRoot,
    .danglingSuccessor,
    .unknownOperation,
    .entryTypeMismatch,
    .termTypeMismatch,
    .branchTestType,
    .unknownVariable,
    .argumentArity,
    .argumentTypeMismatch,
    .unchosenCycle
  ] := rfl

#guard scan.length == 18

/-! V5: the two new argument-typing arms. -/

#check (@ArgumentFailureValid.catchAnswer :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty} {edge : Nat} {target : BlockId}
      {operation : OperationId} {request : Var} {args : List Var}
      {onError : BlockId} {errorArgs : List Var}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty} {declared : Ty},
    block.term = .performCatch operation request target args onError errorArgs →
    ¬ edge = 1 →
    alphabet.lookup operation = some operationDef →
    lookupBlock raw target = some targetBlock →
    (RawBlock.params targetBlock)[args.length]? = some declared →
    alphabet.answerTy operationDef ≠ declared →
    ArgumentFailureValid alphabet raw block edge target args.length
      (.typeMismatch (alphabet.answerTy operationDef) declared))

#check (@ArgumentFailureValid.catchError :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty} {edge : Nat} {target : BlockId}
      {operation : OperationId} {request : Var} {valueTarget : BlockId}
      {args : List Var} {errorArgs : List Var}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty} {declared : Ty},
    block.term = .performCatch operation request valueTarget args target errorArgs →
    edge = 1 →
    alphabet.lookup operation = some operationDef →
    lookupBlock raw target = some targetBlock →
    (RawBlock.params targetBlock)[errorArgs.length]? = some declared →
    alphabet.errorTy operationDef ≠ declared →
    ArgumentFailureValid alphabet raw block edge target errorArgs.length
      (.typeMismatch (alphabet.errorTy operationDef) declared))

/-- Flow v3's term clause is five-fold: the fifth is the branch test. -/
example {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty) (raw : RawFlow Ty) :
    TermsWF alphabet raw ↔
      ((∀ block, block ∈ raw.blocks → block.VarsWF) ∧
       (∀ block, block ∈ raw.blocks → ArityWF raw block) ∧
       (∀ block, block ∈ raw.blocks → ArgumentsWF alphabet raw block) ∧
       (∀ block, block ∈ raw.blocks → OperandsWF alphabet raw block) ∧
       (∀ block, block ∈ raw.blocks → BranchTestWF alphabet block)) :=
  Iff.rfl

end Clauses

section Admission

/-! V6: executable admission receipts over a fallible alphabet. -/

inductive TyCode where
  | nat
  | unit
  | bool
  | str
deriving DecidableEq, Repr

inductive ExampleOp where
  | probe
  | run
deriving DecidableEq, Repr

def alphabetId (value : Nat) : AlphabetId := ⟨value⟩

def exampleLookup : OperationId → Option ExampleOp
  | ⟨0⟩ => some .probe
  | ⟨1⟩ => some .run
  | _ => none

/-- `probe : nat → bool` fails with `unit`; `run : nat → nat` fails with
`str`. Only the error row makes a caught failure typeable. -/
def ExampleAlphabet : FlowAlphabet TyCode where
  id := alphabetId 9
  Op := ExampleOp
  operationId
    | .probe => operationId 0
    | .run => operationId 1
  lookup := exampleLookup
  requestTy
    | .probe => .nat
    | .run => .nat
  answerTy
    | .probe => .bool
    | .run => .nat
  errorTy
    | .probe => .unit
    | .run => .str
  boolTy := .bool
  lookup_operationId := by
    intro operation
    cases operation <;> rfl
  operationId_of_lookup := by
    intro id operation found
    cases operation <;> rcases id with ⟨_ | _ | value⟩ <;>
      simp [exampleLookup] at found <;> rfl

def probe : OperationId := operationId 0
def run : OperationId := operationId 1

def block (id : Nat) (params : List TyCode) (term : RawTerm) : RawBlock TyCode :=
  ⟨blockId id, params, term⟩

def rawFlow (blocks : List (RawBlock TyCode)) : RawFlow TyCode :=
  ⟨alphabetId 9, [blockId 0], blockId 0, .nat, .nat, blocks⟩

def isAdmitted (raw : RawFlow TyCode) : Bool :=
  match admit ExampleAlphabet raw with
  | .ok _ => true
  | .error _ => false

def rejectedWith (diagnostic : Diagnostic TyCode) (raw : RawFlow TyCode) : Bool :=
  match admit ExampleAlphabet raw with
  | .error found => decide (found = diagnostic)
  | .ok _ => false

/-- The reference v3 graph: probe the input, branch on the answer, and on the
`true` side `run` it with a failure successor that keeps the input alongside
the error. Both new terminators, both edges of the catch, and the branch site
in one document. -/
def catchAndBranch : RawFlow TyCode :=
  rawFlow [
    block 0 [.nat] (.perform probe ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.nat, .bool] (.branch ⟨1⟩ (decisionId 0) (blockId 2) (blockId 3) [⟨0⟩]),
    block 2 [.nat] (.performCatch run ⟨0⟩ (blockId 4) [] (blockId 5) [⟨0⟩]),
    block 3 [.nat] (.ret ⟨0⟩),
    block 4 [.nat] (.ret ⟨0⟩),
    block 5 [.nat, .str] (.ret ⟨0⟩)
  ]

#guard isAdmitted catchAndBranch

/-- The error slot is typed by the operation's `errorTy`, not by its
`answerTy`: block 5's second parameter must be `str`. -/
def wrongErrorSlot : RawFlow TyCode :=
  rawFlow [
    block 0 [.nat] (.perform probe ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.nat, .bool] (.branch ⟨1⟩ (decisionId 0) (blockId 2) (blockId 3) [⟨0⟩]),
    block 2 [.nat] (.performCatch run ⟨0⟩ (blockId 4) [] (blockId 5) [⟨0⟩]),
    block 3 [.nat] (.ret ⟨0⟩),
    block 4 [.nat] (.ret ⟨0⟩),
    block 5 [.nat, .nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith
  ⟨.argumentTypeMismatch, .argument (blockId 2) 1 1, .typeMismatch .str .nat⟩
  wrongErrorSlot

/-- The two edges have their own arities: the failure edge of block 2 carries
`errorArgs ++ [error]`, so block 5 declares two parameters and not one. -/
def wrongErrorArity : RawFlow TyCode :=
  rawFlow [
    block 0 [.nat] (.perform probe ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.nat, .bool] (.branch ⟨1⟩ (decisionId 0) (blockId 2) (blockId 3) [⟨0⟩]),
    block 2 [.nat] (.performCatch run ⟨0⟩ (blockId 4) [] (blockId 5) [⟨0⟩]),
    block 3 [.nat] (.ret ⟨0⟩),
    block 4 [.nat] (.ret ⟨0⟩),
    block 5 [.str] (.ret ⟨0⟩)
  ]

#guard rejectedWith
  ⟨.argumentArity, .successor (blockId 2) 1, .arity 2 1⟩
  wrongErrorArity

/-- The value edge keeps the answer typing it had as a plain `perform`. -/
def wrongAnswerSlot : RawFlow TyCode :=
  rawFlow [
    block 0 [.nat] (.perform probe ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.nat, .bool] (.branch ⟨1⟩ (decisionId 0) (blockId 2) (blockId 3) [⟨0⟩]),
    block 2 [.nat] (.performCatch run ⟨0⟩ (blockId 4) [] (blockId 5) [⟨0⟩]),
    block 3 [.nat] (.ret ⟨0⟩),
    block 4 [.str] (.ret ⟨0⟩),
    block 5 [.nat, .str] (.ret ⟨0⟩)
  ]

#guard rejectedWith
  ⟨.argumentTypeMismatch, .argument (blockId 2) 0 0, .typeMismatch .nat .str⟩
  wrongAnswerSlot

/-- A `performCatch` of an operation outside the alphabet is refused by the
same clause a `perform` is. -/
def unknownCatch : RawFlow TyCode :=
  rawFlow [
    block 0 [.nat] (.performCatch (operationId 7) ⟨0⟩ (blockId 1) [] (blockId 2) [⟨0⟩]),
    block 1 [.nat] (.ret ⟨0⟩),
    block 2 [.nat, .str] (.ret ⟨0⟩)
  ]

#guard rejectedWith
  ⟨.unknownOperation, .operation (blockId 0), .operation (operationId 7)⟩
  unknownCatch

/-- Two decision sites collide whichever terminator declares them: the
`branch` at block 1 repeats the `choose` site at block 0. -/
def collidingSites : RawFlow TyCode :=
  rawFlow [
    block 0 [.nat] (.choose (decisionId 0) (blockId 1) (blockId 1) [⟨0⟩]),
    block 1 [.nat] (.perform probe ⟨0⟩ (blockId 2) [⟨0⟩]),
    block 2 [.nat, .bool] (.branch ⟨1⟩ (decisionId 0) (blockId 3) (blockId 3) [⟨0⟩]),
    block 3 [.nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith
  ⟨.duplicateDecisionId, .decision (blockId 2), .decision (decisionId 0)⟩
  collidingSites

end Admission

end EffectsTest.Flow.FlowV3Contract
