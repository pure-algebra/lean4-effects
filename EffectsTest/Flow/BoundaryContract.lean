/-
Contract packet: `test/contracts/effects-boundary.contract.md` (Effects
v0.8.0, light ceremony). The consumer boundary: what the package publishes,
what it hides, and the two clause structures a consumer reads instead of a
checker. Receipts are `#check` ascriptions, `rfl`, `decide` and `#guard`.
-/

import Effects

set_option autoImplicit false

namespace EffectsTest.Flow.BoundaryContract

open Effects

universe u uTy uOp

/-! ## The pigeonhole pair is public and generic (finding #39) -/

#check (@Effects.ListAux.length_filter_ne :
  ∀ {α : Type u} [_inst : DecidableEq α] {a : α} {l : List α}, a ∈ l →
    (l.filter fun x => decide (x ≠ a)).length + 1 ≤ l.length)

#check (@Effects.ListAux.length_le_of_nodup_subset :
  ∀ {α : Type u} [_inst : DecidableEq α] {l₁ l₂ : List α},
    l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length)

/-! ## The flow alphabet's embedding is upstream (finding #38) -/

#check (@FlowAlphabet.toAlphabet :
  ∀ {Ty : Type uTy}, FlowAlphabet.{uTy, uOp} Ty → Alphabet.{uTy, uOp} Ty)

example {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty) :
    alphabet.toAlphabet = ⟨alphabet.Op, alphabet.requestTy, alphabet.answerTy⟩ := rfl

#check @FlowAlphabet.toFamily

/-! ## Block resolution and reachability (findings #38, #39) -/

#check (@lookupBlock_id :
  ∀ {Ty : Type uTy} {raw : RawFlow Ty} {id : BlockId} {block : RawBlock Ty},
    lookupBlock raw id = some block → block.id = id)

#check (@mem_blockIds_of_lookup :
  ∀ {Ty : Type uTy} {raw : RawFlow Ty} {id : BlockId} {block : RawBlock Ty},
    lookupBlock raw id = some block → id ∈ raw.blocks.map RawBlock.id)

#check (@reachableNoChoose_trans :
  ∀ {Ty : Type uTy} {raw : RawFlow Ty} {source middle target : BlockId},
    ReachableNoChoose raw source middle → ReachableNoChoose raw middle target →
      ReachableNoChoose raw source target)

#check (@RawFlow.nodup_reachSet :
  ∀ {Ty : Type uTy} (raw : RawFlow Ty) (start : BlockId), (raw.reachSet start).Nodup)

/-! The measure every downstream flow runner terminates on. -/
#check (@RawFlow.reachSet_length_lt_of_edge :
  ∀ {Ty : Type uTy} {raw : RawFlow Ty}, CyclesWF raw →
    ∀ {source target : BlockId}, EdgeNoChoose raw source target →
      (raw.reachSet target).length < (raw.reachSet source).length)

/-- The saturation scaffolding is gone from the public surface. `reachSet` and
its membership law are what remain, and they still compute. -/
example : (⟨⟨0⟩, [⟨0⟩], ⟨0⟩, (), (),
    [ { id := ⟨0⟩, params := [], term := .jump ⟨1⟩ [] }
    , { id := ⟨1⟩, params := [], term := .ret ⟨0⟩ } ]⟩ : RawFlow Unit).reachSet ⟨0⟩ =
    [⟨0⟩, ⟨1⟩] := by decide

/-! ## The region clauses are a structure with a soundness law (finding #36) -/

#check (@regionWF_iff_check :
  ∀ {Ty : Type uTy} [_inst : DecidableEq Ty] (alphabet : FlowAlphabet Ty)
      (flow : RegionFlow Ty), RegionWF alphabet flow ↔ flow.check alphabet = none)

/-! The fourteen fields, in `RegionClause` order. Each is a projection a
consumer applies; none of them mentions `check`. -/

#check @RegionWF.duplicateRegion
#check @RegionWF.unknownParent
#check @RegionWF.continueOutside
#check @RegionWF.continueTyped
#check @RegionWF.entryInside
#check @RegionWF.unknownLabel
#check @RegionWF.retInside
#check @RegionWF.successorLabel
#check @RegionWF.enterParent
#check @RegionWF.enterBody
#check @RegionWF.acquireOutside
#check @RegionWF.acquireRelease
#check @RegionWF.leaveOutside
#check @RegionWF.leaveTyped

/-- One field per clause: `RegionClause` and `RegionWF` have the same arity. -/
example : ([ .duplicateRegion, .unknownParent, .continueOutside, .continueTyped
           , .unknownLabel, .entryInside, .successorLabel, .enterParent
           , .enterBody, .acquireOutside, .acquireRelease, .leaveOutside
           , .leaveTyped, .retInside ] : List RegionClause).length = 14 := rfl

/-! `TargetsLabelled` is the Prop a consumer reads instead of the Bool, and
`targetsLabelled_iff` is the bridge. -/

#check (@RegionFlow.targetsLabelled_iff :
  ∀ {Ty : Type uTy} [_inst : DecidableEq Ty] {flow : RegionFlow Ty}
      {label : Option RegionId} {targets : List BlockId},
    flow.targetsLabelled label targets = true ↔ flow.TargetsLabelled label targets)

/-! ## `errorTy` is an `Option`, and a catch on an unfailable operation is
refused (finding #43, `EF-FLOW-CE-010`) -/

#check (@FlowAlphabet.errorTy :
  ∀ {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty), alphabet.Op → Option Ty)

#check (@AdmissionClause.catchUnfailable : AdmissionClause)

#guard scan.length == 19

/-- `catchUnfailable` sits between `branchTestType` and `unknownVariable`: it
needs the operation to be in the alphabet (`unknownOperation`, earlier) and it
guards the error slot that `argumentTypeMismatch` compares (later). -/
example : (scan.drop 12).take 4 =
    [.termTypeMismatch, .branchTestType, .catchUnfailable, .unknownVariable] := rfl

section Unfailable

inductive Code where
  | nat
  | bool
deriving DecidableEq, Repr

inductive Op where
  /-- `total : nat → nat`, and it cannot fail. -/
  | total
  /-- `risky : nat → nat`, failing with a `nat`. -/
  | risky
deriving DecidableEq, Repr

def look : OperationId → Option Op
  | ⟨0⟩ => some .total
  | ⟨1⟩ => some .risky
  | _ => none

def alphabet : FlowAlphabet Code where
  id := ⟨0⟩
  Op := Op
  operationId
    | .total => ⟨0⟩
    | .risky => ⟨1⟩
  lookup := look
  requestTy _ := .nat
  answerTy _ := .nat
  errorTy
    | .total => none
    | .risky => some .nat
  boolTy := .bool
  lookup_operationId := by intro operation; cases operation <;> rfl
  operationId_of_lookup := by
    intro id operation found
    cases operation <;> rcases id with ⟨_ | _ | value⟩ <;> simp [look] at found <;> rfl

def flowCatching (operation : Nat) : RawFlow Code :=
  ⟨⟨0⟩, [⟨0⟩], ⟨0⟩, .nat, .nat,
    [ { id := ⟨0⟩, params := [.nat],
        term := .performCatch ⟨operation⟩ ⟨0⟩ ⟨1⟩ [] ⟨2⟩ [] }
    , { id := ⟨1⟩, params := [.nat], term := .ret ⟨0⟩ }
    , { id := ⟨2⟩, params := [.nat], term := .ret ⟨0⟩ } ]⟩

def refusal? (raw : RawFlow Code) : Option (Diagnostic Code) :=
  match admit alphabet raw with
  | .error diagnostic => some diagnostic
  | .ok _ => none

/-! A catch on `risky`, whose `errorTy` is `some .nat`, is admitted. -/
#guard refusal? (flowCatching 1) = none

/-! `EF-FLOW-CE-010`: a catch on `total`, whose `errorTy` is `none`, is refused
by `catchUnfailable` at the block's own term site, naming the operation. Under
the v0.7.0 total `errorTy` this flow was admitted, because every operation
declared some error type and the boundary only ever compared spellings. -/
#guard refusal? (flowCatching 0) =
  some ⟨.catchUnfailable, .term ⟨0⟩, .operation ⟨0⟩⟩

/-- The clause is a clause of `FlowWF`: the refused flow fails `CatchableWF`,
which is what `catchUnfailable` decides. -/
example : ¬ CatchableWF alphabet
    { id := ⟨0⟩, params := [.nat],
      term := .performCatch ⟨0⟩ ⟨0⟩ ⟨1⟩ [] ⟨2⟩ [] } := by
  show ¬ (match alphabet.lookup ⟨0⟩ with
    | some operationDef => (alphabet.errorTy operationDef).isSome = true
    | none => True)
  have : alphabet.lookup ⟨0⟩ = some Op.total := rfl
  simp [this]
  rfl

end Unfailable

end EffectsTest.Flow.BoundaryContract
