import Effects.Flow.Admission
import Effects.Flow.Block
import Effects.Flow.Checked
import Effects.Flow.Raw
import Effects.Flow.Region

/-!
# Flow v3 attacks

Witnesses for `EF-FLOW-CE-007` and `EF-FLOW-CE-008` in
`test/counterexamples/REGISTER.md`; attack shapes in
`test/counterexamples/flow/ATTACKS.md`; packet
`test/contracts/flow-v3.contract.md`.

Both attacks are about the two terminators Flow v3 adds.

* `EF-FLOW-CE-007` — *a caught failure unwinds regions.* A `performCatch`
  names a failure successor, so a failure that is caught does not close the
  enclosing region: control simply continues at the named block. The attack
  is the reading in which the failure edge is allowed to leave the region;
  the region layer condemns it with `successorLabel`, exactly as it condemns
  a plain successor that changes label.
* `EF-FLOW-CE-008` — *a branch on a value escapes the tape bound.* A `branch`
  is taken by a value, so the reading in which it is not a decision makes a
  loop closed by a `branch` need no tape entry at all. `isChoose` is true for
  `branch`, so `CyclesWF` counts it: the branch loop admits and the same
  graph with a `jump` is refused.
-/

set_option autoImplicit false

namespace EffectsTest.Counterexamples.Flow.V3

open Effects

/-! ## A four-spelling alphabet with a fallible operation -/

inductive TyCode where
  | nat
  | unit
  | bool
  | str
deriving DecidableEq, Repr

inductive ExampleOp where
  /-- `probe : nat → bool`, error `unit`. -/
  | probe
  /-- `run : nat → nat`, error `str`: the one operation worth catching. -/
  | run
deriving DecidableEq, Repr

def blockId (value : Nat) : BlockId := ⟨value⟩
def operationId (value : Nat) : OperationId := ⟨value⟩
def alphabetId (value : Nat) : AlphabetId := ⟨value⟩
def decisionId (value : Nat) : DecisionId := ⟨value⟩
def regionId (value : Nat) : RegionId := ⟨value⟩

def exampleLookup : OperationId → Option ExampleOp
  | ⟨0⟩ => some .probe
  | ⟨1⟩ => some .run
  | _ => none

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

def rawFlow (roots : List BlockId) (entry : BlockId)
    (inputTy resultTy : TyCode) (blocks : List (RawBlock TyCode)) : RawFlow TyCode :=
  ⟨alphabetId 9, roots, entry, inputTy, resultTy, blocks⟩

def isAdmitted (raw : RawFlow TyCode) : Bool :=
  match admit ExampleAlphabet raw with
  | .ok _ => true
  | .error _ => false

def rejectedWith (diagnostic : Diagnostic TyCode) (raw : RawFlow TyCode) : Bool :=
  match admit ExampleAlphabet raw with
  | .error found => decide (found = diagnostic)
  | .ok _ => false

/-! ## EF-FLOW-CE-008 — a branch on a value escapes the tape bound

The attacked reading: a `branch` is a test of a value, not a question for the
tape, so a loop closed by a `branch` is bounded by the values it computes and
needs no decision entry. Nothing in the carrier can see those values, so such
a loop would have no finite bound at all. Flow v3 answers by making `branch` a
decision *site* as well as a value test: `isChoose` is true for it, the site is
a `decision?`, and `CyclesWF` counts it. -/

#guard RawTerm.isChoose (.branch ⟨1⟩ (decisionId 0) (blockId 0) (blockId 2) [⟨0⟩]) == true
#guard RawTerm.decision? (.branch ⟨1⟩ (decisionId 0) (blockId 0) (blockId 2) [⟨0⟩]) ==
  some (decisionId 0)
#guard RawTerm.successors (.branch ⟨1⟩ (decisionId 0) (blockId 0) (blockId 2) [⟨0⟩]) ==
  [blockId 0, blockId 2]

/-- The loop closes through a `branch`, so a finite tape bounds it. -/
def branchLoop : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .nat .nat [
    block 0 [.nat] (.perform probe ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.nat, .bool] (.branch ⟨1⟩ (decisionId 0) (blockId 0) (blockId 2) [⟨0⟩]),
    block 2 [.nat] (.ret ⟨0⟩)
  ]

#guard isAdmitted branchLoop
#guard cyclesChoose branchLoop == true

/-- The same graph with the branch replaced by an unconditional jump: the
cycle now passes through no decision and is refused at its first declared
block. This is the shape the attacked reading would have admitted. -/
def jumpLoop : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .nat .nat [
    block 0 [.nat] (.perform probe ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.nat, .bool] (.jump (blockId 0) [⟨0⟩]),
    block 2 [.nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.unchosenCycle, .block 0, .block (blockId 0)⟩ jumpLoop
#guard cyclesChoose jumpLoop == false

/-- The branch test carries the alphabet's boolean spelling; testing the `nat`
parameter instead is refused by the one clause Flow v3 adds. -/
def branchOnNat : RawFlow TyCode :=
  rawFlow [blockId 0] (blockId 0) .nat .nat [
    block 0 [.nat] (.perform probe ⟨0⟩ (blockId 1) [⟨0⟩]),
    block 1 [.nat, .bool] (.branch ⟨0⟩ (decisionId 0) (blockId 0) (blockId 2) [⟨0⟩]),
    block 2 [.nat] (.ret ⟨0⟩)
  ]

#guard rejectedWith ⟨.branchTestType, .term (blockId 1), .typeMismatch .bool .nat⟩
  branchOnNat

/-! ## EF-FLOW-CE-007 — a caught failure unwinds regions

The attacked reading: an operation that fails inside a region closes that
region, so the failure successor of a `performCatch` is reached with the
region already unwound and may be labelled with the enclosing scope (or with
none at all). Flow v3 rejects it: the failure edge is a declared successor
like any other, so the region layer requires it to carry the block's own
label, and a caught failure therefore continues *inside* the region that is
still open. -/

def regionBlock (id : Nat) (region : Option Nat) (params : List TyCode)
    (term : RegionTerm) : RegionBlock TyCode :=
  ⟨blockId id, region.map regionId, params, term⟩

/-- Region 1 wraps a fallible `run`; both of its successors stay inside it. -/
def caughtInside : RegionFlow TyCode :=
  { alphabet := alphabetId 9
    roots := [blockId 0]
    entry := blockId 0
    inputTy := .nat
    resultTy := .nat
    regions := [⟨regionId 1, none, blockId 5, .nat⟩]
    blocks := [
      regionBlock 0 none [.nat] (.enter (regionId 1) (blockId 1) [⟨0⟩]),
      regionBlock 1 (some 1) [.nat]
        (.plain (.performCatch run ⟨0⟩ (blockId 2) [] (blockId 3) [⟨0⟩])),
      regionBlock 2 (some 1) [.nat] (.leave ⟨0⟩),
      regionBlock 3 (some 1) [.nat, .str] (.leave ⟨0⟩),
      regionBlock 5 none [.nat] (.plain (.ret ⟨0⟩))
    ] }

def admittedRegions (flow : RegionFlow TyCode) : Bool :=
  match admitRegions ExampleAlphabet flow with
  | .ok _ => true
  | .error _ => false

def regionRefusal (flow : RegionFlow TyCode) : Option RegionDiagnostic :=
  match admitRegions ExampleAlphabet flow with
  | .error (.region diagnostic) => some diagnostic
  | _ => none

#guard admittedRegions caughtInside

/-- The attack: the failure successor is placed outside region 1, as it would
be if a caught failure had already closed it. -/
def caughtOutside : RegionFlow TyCode :=
  { caughtInside with
    blocks := [
      regionBlock 0 none [.nat] (.enter (regionId 1) (blockId 1) [⟨0⟩]),
      regionBlock 1 (some 1) [.nat]
        (.plain (.performCatch run ⟨0⟩ (blockId 2) [] (blockId 3) [⟨0⟩])),
      regionBlock 2 (some 1) [.nat] (.leave ⟨0⟩),
      regionBlock 3 none [.nat, .str] (.plain (.ret ⟨0⟩)),
      regionBlock 5 none [.nat] (.plain (.ret ⟨0⟩))
    ] }

#guard regionRefusal caughtOutside ==
  some ⟨.successorLabel, some (blockId 1), some (regionId 1)⟩

end EffectsTest.Counterexamples.Flow.V3
