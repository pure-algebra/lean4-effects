import Effects.Flow.Admission
import Effects.Flow.Block
import Effects.Flow.Checked
import Effects.Flow.Raw

/-!
# Flow v2 attacks

Witnesses for `EF-FLOW-CE-001` through `EF-FLOW-CE-003` in
`test/counterexamples/REGISTER.md`; attack shapes in
`test/counterexamples/flow/ATTACKS.md`; packet
`test/contracts/flow-v2.contract.md`.

This module also carries the packet's executable admission receipts
(`#guard` over `admit`) and the retained v1 rows over the v2 carrier. They
cannot be red purely by missing names: a `def` body and a `#guard` line are
elaborated with error recovery, so while the carrier is v0.3.1 every
definition and guard below is red for the missing v2 names and for the
consequential arity and evaluation diagnostics. The v0.3.1 evidence of
`EF-FLOW-CE-002` (a `jump` self-loop admits) is a transcript in
`ATTACKS.md`, executed against commit `9595a88`, because a v1-shaped witness
cannot be kept in a v2 module.

Red until the builder lands Flow v2: every `def`, `#guard`, and `example`
in this module.
-/

set_option autoImplicit false

namespace EffectsTest.Counterexamples.Flow

open Effects

inductive TyCode where
  | nat
  | unit
  /-- Flow v3: the spelling `FlowAlphabet.boolTy` names. -/
  | bool
deriving DecidableEq, Repr

inductive ExampleOp where
  | get
  | put
deriving DecidableEq, Repr

def blockId (value : Nat) : BlockId := ⟨value⟩
def operationId (value : Nat) : OperationId := ⟨value⟩
def alphabetId (value : Nat) : AlphabetId := ⟨value⟩
def decisionId (value : Nat) : DecisionId := ⟨value⟩

def exampleLookup : OperationId → Option ExampleOp
  | ⟨0⟩ => some .get
  | ⟨1⟩ => some .put
  | _ => none

/-- `get : unit → nat` is operation 0; `put : nat → unit` is operation 1. -/
def ExampleAlphabet : FlowAlphabet TyCode where
  id := alphabetId 7
  Op := ExampleOp
  operationId
    | .get => operationId 0
    | .put => operationId 1
  lookup := exampleLookup
  requestTy
    | .get => .unit
    | .put => .nat
  answerTy
    | .get => .nat
    | .put => .unit
  errorTy _ := .unit
  boolTy := .bool
  lookup_operationId := by
    intro operation
    cases operation <;> rfl
  operationId_of_lookup := by
    intro id operation found
    cases operation <;> rcases id with ⟨_ | _ | value⟩ <;>
      simp [exampleLookup] at found <;> rfl

def get : OperationId := operationId 0
def put : OperationId := operationId 1

def block (id : Nat) (params : List TyCode) (term : RawTerm) : RawBlock TyCode :=
  ⟨blockId id, params, term⟩

def rawFlow (roots : List BlockId) (entry : BlockId)
    (inputTy resultTy : TyCode) (blocks : List (RawBlock TyCode))
    (alphabet : AlphabetId := alphabetId 7) : RawFlow TyCode :=
  ⟨alphabet, roots, entry, inputTy, resultTy, blocks⟩

def isAdmitted (raw : RawFlow TyCode) : Bool :=
  match admit ExampleAlphabet raw with
  | .ok _ => true
  | .error _ => false

def rejectedWith (diagnostic : Diagnostic TyCode) (raw : RawFlow TyCode) : Bool :=
  match admit ExampleAlphabet raw with
  | .error found => decide (found = diagnostic)
  | .ok _ => false

def clauseAt (clause : AdmissionClause) (raw : RawFlow TyCode) :
    Option (Diagnostic TyCode) :=
  diagnoseAt ExampleAlphabet raw clause

/-! ### `RawTerm.successors` on the four-ary terms (D2, executable pin). -/

#guard RawTerm.successors (.ret ⟨0⟩) == []
#guard RawTerm.successors (.jump (blockId 1) [⟨0⟩]) == [blockId 1]
#guard RawTerm.successors (.perform get ⟨0⟩ (blockId 1) [⟨0⟩]) == [blockId 1]
#guard RawTerm.successors (.choose (decisionId 0) (blockId 1) (blockId 2) [⟨0⟩]) ==
  [blockId 1, blockId 2]

/-! ## EF-FLOW-CE-001 — one payload can carry the environment

Under v0.3.1 the target of `perform` receives only the answer
(`Effects/Flow/Block.lean` at `9595a88`: `RawTerm.perform (operation)
(target)` and one `inputTy` per block), so `let x ← get; put x; return x`
has no block that holds `x` while `put` runs. The repair is block
parameters: `incr` performs `get` into a fresh parameter, hands that
parameter to `put` as the request while passing the entry parameter and the
answer along, and returns the answer of `get` from the block after `put`. -/

def incr : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .nat [
    block 0 [.unit] (.perform get ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.unit, .nat] (.perform put ⟨1⟩ (blockId 2) [⟨0⟩, ⟨1⟩]),
    block 2 [.unit, .nat, .unit] (.ret ⟨1⟩)
  ]

#guard isAdmitted incr

/-- The value returned is the one that crossed `put`: dropping it from the
argument list makes block 2's `ret ⟨1⟩` name a missing parameter. -/
def incrDropped : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .nat [
    block 0 [.unit] (.perform get ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.unit, .nat] (.perform put ⟨1⟩ (blockId 2) [⟨0⟩]),
    block 2 [.unit, .unit] (.ret ⟨1⟩)
  ]

#guard rejectedWith ⟨.termTypeMismatch, .term (blockId 2), .typeMismatch .nat .unit⟩
  incrDropped

/-! ## EF-FLOW-CE-002 — a tape bounds every run without a cycle clause

v0.3.1 admits a `jump` self-loop (`ATTACKS.md` transcript; lean4-effect4
`E4-FLOW-CE-005`). No finite decision tape bounds a run of it. v2 rejects
every cycle that passes through no `choose`, over the whole document, and
admits a cycle through a decision. -/

def unchosenLoop : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.jump (blockId 0) [⟨0⟩])
  ]

#guard rejectedWith ⟨.unchosenCycle, .block 0, .block (blockId 0)⟩ unchosenLoop

-- `unchosenCycle` is the first diagnostic: the sixteen earlier clauses pass.
#guard (scan.take 16).all fun clause => (clauseAt clause unchosenLoop).isNone

#guard cyclesChoose unchosenLoop == false

def chosenLoop : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.choose (decisionId 0) (blockId 0) (blockId 1) [⟨0⟩]),
    block 1 [.unit] (.ret ⟨0⟩)
  ]

#guard isAdmitted chosenLoop

/-- A `perform` edge is not a decision: the two-block cycle through `get` is
condemned at its first declared block. -/
def performLoop : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.perform get ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.unit, .nat] (.jump (blockId 0) [⟨0⟩])
  ]

#guard rejectedWith ⟨.unchosenCycle, .block 0, .block (blockId 0)⟩ performLoop

/-- Whole-document: an unreachable unchosen cycle is rejected. This reverses
the cycle half of `E4-FLOW-CE-014`. -/
def unreachableUnchosenLoop : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.ret ⟨0⟩),
    block 1 [.nat] (.jump (blockId 1) [⟨0⟩])
  ]

#guard rejectedWith ⟨.unchosenCycle, .block 1, .block (blockId 1)⟩
  unreachableUnchosenLoop

/-- Source order: block 0 leads into the cycle but is not on it; block 1 is
the first declared block on the cycle `1 → 2 → 1`. -/
def lateLoop : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.jump (blockId 2) [⟨0⟩]),
    block 1 [.unit] (.jump (blockId 2) [⟨0⟩]),
    block 2 [.unit] (.jump (blockId 1) [⟨0⟩])
  ]

#guard rejectedWith ⟨.unchosenCycle, .block 1, .block (blockId 1)⟩ lateLoop

/-- A cycle that passes through a decision somewhere is admitted even when
some of its edges are `jump`s. -/
def chosenTwoBlockLoop : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.jump (blockId 1) [⟨0⟩]),
    block 1 [.unit] (.choose (decisionId 0) (blockId 0) (blockId 2) [⟨0⟩]),
    block 2 [.unit] (.ret ⟨0⟩)
  ]

#guard isAdmitted chosenTwoBlockLoop

/-! ## EF-FLOW-CE-003 — argument arity can be checked without types

A count check accepts an argument list of the right length and the wrong
types. The repair is a positional clause, `argumentTypeMismatch`, ordered
after `argumentArity`; the two clauses are independent under `diagnoseAt`. -/

def rightArityWrongType : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .nat [
    block 0 [.unit] (.jump (blockId 1) [⟨0⟩]),
    block 1 [.nat] (.ret ⟨0⟩)
  ]

#guard (clauseAt .argumentArity rightArityWrongType).isNone
#guard rejectedWith
  ⟨.argumentTypeMismatch, .argument (blockId 0) 0 0, .typeMismatch .unit .nat⟩
  rightArityWrongType

def wrongArity : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.jump (blockId 1) [⟨0⟩]),
    block 1 [.unit, .unit] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.argumentArity, .successor (blockId 0) 0, .arity 1 2⟩ wrongArity
#guard (clauseAt .argumentTypeMismatch wrongArity).isNone

/-! ## Clause receipts for the v2 diagnostics

Exact site and payload for each new failure form, in the packet's frozen
orientation: a target's parameter list is the `actual` side. -/

def unknownVariableFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.ret ⟨1⟩)
  ]

#guard rejectedWith ⟨.unknownVariable, .term (blockId 0), .variable ⟨1⟩⟩
  unknownVariableFlow

-- Operand typing is guarded by variable range: the term clause is silent.
#guard (clauseAt .termTypeMismatch unknownVariableFlow).isNone

/-- Operand order: the request is checked before the arguments, and the
first out-of-range occurrence is reported by value. -/
def unknownArgumentFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .nat [
    block 0 [.unit] (.perform get ⟨0⟩ (blockId 1) [⟨3⟩]),
    block 1 [.nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.unknownVariable, .term (blockId 0), .variable ⟨3⟩⟩
  unknownArgumentFlow

def entryArityFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit, .unit] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.entryTypeMismatch, .entry, .arity 1 2⟩ entryArityFlow

def entryTypeFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .nat [
    block 0 [.nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.entryTypeMismatch, .entry, .typeMismatch .unit .nat⟩
  entryTypeFlow

def retTypeFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .nat .unit [
    block 0 [.nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.termTypeMismatch, .term (blockId 0), .typeMismatch .unit .nat⟩
  retTypeFlow

def requestTypeFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .nat .nat [
    block 0 [.nat] (.perform get ⟨0⟩ (blockId 1) []),
    block 1 [.nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.termTypeMismatch, .term (blockId 0), .typeMismatch .unit .nat⟩
  requestTypeFlow

/-- `E4-FLOW-CE-004` moved: the answer of `get` lands in the answer slot,
position `args.length` of successor 0. -/
def answerSlotFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.perform get ⟨0⟩ (blockId 1) []),
    block 1 [.unit] (.ret ⟨0⟩)
  ]

#guard rejectedWith
  ⟨.argumentTypeMismatch, .argument (blockId 0) 0 0, .typeMismatch .nat .unit⟩
  answerSlotFlow

/-- The receiver is part of the site: `choose` delivers one argument list to
two blocks, and the right receiver's mismatch names successor 1. -/
def chooseRightFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.choose (decisionId 0) (blockId 1) (blockId 2) [⟨0⟩]),
    block 1 [.unit] (.ret ⟨0⟩),
    block 2 [.nat] (.jump (blockId 1) [⟨0⟩])
  ]

#guard rejectedWith
  ⟨.argumentTypeMismatch, .argument (blockId 0) 1 0, .typeMismatch .unit .nat⟩
  chooseRightFlow

/-- Position 1 of successor 0 is reported after position 0 passes. -/
def secondPositionFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.perform get ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.unit, .nat] (.jump (blockId 2) [⟨0⟩, ⟨1⟩]),
    block 2 [.unit, .unit] (.ret ⟨0⟩)
  ]

#guard rejectedWith
  ⟨.argumentTypeMismatch, .argument (blockId 1) 0 1, .typeMismatch .nat .unit⟩
  secondPositionFlow

/-- A dangling target is owned by `danglingSuccessor`; the term clauses are
clause-local and stay silent on it. -/
def danglingJump : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.jump (blockId 9) [⟨0⟩])
  ]

#guard rejectedWith ⟨.danglingSuccessor, .successor (blockId 0) 0, .block (blockId 9)⟩
  danglingJump
#guard (clauseAt .argumentArity danglingJump).isNone
#guard (clauseAt .argumentTypeMismatch danglingJump).isNone
#guard (clauseAt .termTypeMismatch danglingJump).isNone

/-- An unknown operation is owned by `unknownOperation`; the operand and
answer-slot checks stay silent on it. -/
def unknownOperationFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .nat [
    block 0 [.unit] (.perform (operationId 9) ⟨0⟩ (blockId 1) []),
    block 1 [.nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith
  ⟨.unknownOperation, .operation (blockId 0), .operation (operationId 9)⟩
  unknownOperationFlow
#guard (clauseAt .termTypeMismatch unknownOperationFlow).isNone
#guard (clauseAt .argumentTypeMismatch unknownOperationFlow).isNone

/-! ## Retained v1 rows over the v2 carrier

`E4-FLOW-CE-001`, `-002`, `-003`, `-007`, `-014` (dangling half), and the
`-016` precision receipts, re-expressed with parameter lists. -/

def duplicateBlockFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.ret ⟨0⟩),
    block 0 [.unit] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.duplicateBlockId, .block 1, .block (blockId 0)⟩ duplicateBlockFlow

def firstDiagnosticFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.ret ⟨0⟩),
    block 0 [.unit] (.ret ⟨0⟩)
  ] (alphabet := alphabetId 99)

#guard rejectedWith
  ⟨.alphabetMismatch, .flow, .alphabet (alphabetId 7) (alphabetId 99)⟩
  firstDiagnosticFlow

def danglingRootFlow : RawFlow TyCode :=
  rawFlow [blockId 0, blockId 9] (blockId 0) .unit .unit [
    block 0 [.unit] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.danglingRoot, .root 1, .block (blockId 9)⟩ danglingRootFlow

def unreachableDanglingFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.ret ⟨0⟩),
    block 1 [.nat] (.jump (blockId 9) [⟨0⟩])
  ]

#guard rejectedWith ⟨.danglingSuccessor, .successor (blockId 1) 0, .block (blockId 9)⟩
  unreachableDanglingFlow

def duplicateDecisionFlow : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .unit .unit [
    block 0 [.unit] (.choose (decisionId 5) (blockId 2) (blockId 2) [⟨0⟩]),
    block 1 [.unit] (.choose (decisionId 5) (blockId 2) (blockId 2) [⟨0⟩]),
    block 2 [.unit] (.ret ⟨0⟩)
  ]

#guard clauseAt .duplicateDecisionId duplicateDecisionFlow =
  some ⟨.duplicateDecisionId, .decision (blockId 1), .decision (decisionId 5)⟩

/-- Block 0 is unreachable but first in source order; its left receiver is
checked before its right receiver and before block 2's own defect. -/
def nestedSourceOrderFlow : RawFlow TyCode :=
  rawFlow [blockId 3] (blockId 3) .nat .nat [
    block 0 [.unit] (.choose (decisionId 8) (blockId 1) (blockId 2) [⟨0⟩]),
    block 1 [.nat] (.ret ⟨0⟩),
    block 2 [.nat] (.jump (blockId 3) [⟨0⟩]),
    block 3 [.nat] (.ret ⟨0⟩)
  ]

#guard clauseAt .argumentTypeMismatch nestedSourceOrderFlow =
  some ⟨.argumentTypeMismatch, .argument (blockId 0) 0 0, .typeMismatch .unit .nat⟩

/-- The unrelated-fallback mutation cannot satisfy the validity index. -/
example : ¬ Diagnostic.Valid ExampleAlphabet unchosenLoop
    ⟨.unchosenCycle, .flow, .none⟩ := by
  intro invalid
  cases invalid

end EffectsTest.Counterexamples.Flow
