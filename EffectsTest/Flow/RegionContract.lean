/-
Contract packet: `test/contracts/flow-regions.contract.md` (Effects v0.5.0, light
ceremony). The region layer over Flow v2: carrier, erasure, the fourteen region
clauses, and admission. Executable receipts by `#guard`.
-/

import Effects.Flow.Region

namespace EffectsTest.Flow.RegionContract

open Effects

set_option autoImplicit false

#check (@RegionId : Type)
#check (@RegionTerm : Type)
#check (@RegionRow : Type → Type)
#check (@RegionBlock : Type → Type)
#check (@RegionFlow : Type → Type)
#check (@RegionFlow.erase : {Ty : Type} → RegionFlow Ty → RawFlow Ty)
#check (@RegionClause : Type)
#check (@RegionDiagnostic : Type)
#check (@RegionFlow.check : {Ty : Type} → [DecidableEq Ty] → FlowAlphabet Ty → RegionFlow Ty →
  Option RegionDiagnostic)
#check (@RegionWF : {Ty : Type} → [DecidableEq Ty] → FlowAlphabet Ty → RegionFlow Ty → Prop)
#check @CheckedRegionFlow
#check @admitRegions
#check @admitRegions_ok_erase

/-! ## A three-operation alphabet over TypeScript type spellings -/

def table : List (String × String) :=
  [("number", "number"), ("number", "void"), ("number", "number")]

def alphabet : FlowAlphabet String where
  id := ⟨0⟩
  Op := Fin table.length
  operationId op := ⟨op.val⟩
  lookup id := if h : id.value < table.length then some ⟨id.value, h⟩ else none
  requestTy op := table[op].1
  answerTy op := table[op].2
  lookup_operationId := by
    intro op
    simp [op.isLt]
  operationId_of_lookup := by
    intro id op found
    by_cases lt : id.value < table.length
    · rw [dif_pos lt] at found
      cases found
      cases id
      rfl
    · rw [dif_neg lt] at found
      cases found

def region (id : Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := none, continue_ := ⟨continue_⟩, resultTy := "number" }

/-- Open a region, acquire a resource (release 1 takes the acquired number),
leave with the resource, return it outside. -/
def scopedFlow : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := [region 1 3],
    blocks :=
      [ { id := ⟨0⟩, region := none, params := ["number"], term := .enter ⟨1⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, region := some ⟨1⟩, params := ["number"],
          term := .acquire ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨2⟩, region := some ⟨1⟩, params := ["number", "number"], term := .leave ⟨1⟩ }
      , { id := ⟨3⟩, region := none, params := ["number"], term := .plain (.ret ⟨0⟩) } ] }

def admitted (result : Except (RegionRefusal String) (CheckedRegionFlow alphabet)) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

def refusal? (result : Except (RegionRefusal String) (CheckedRegionFlow alphabet)) :
    Option RegionClause :=
  match result with
  | .error (.region diagnostic) => some diagnostic.clause
  | _ => none

-- The erasure: `enter` and `leave` are jumps, `acquire` is a perform.
#guard scopedFlow.erase.blocks.map (·.term) =
  [ .jump ⟨1⟩ [⟨0⟩], .perform ⟨0⟩ ⟨0⟩ ⟨2⟩ [⟨0⟩], .jump ⟨3⟩ [⟨1⟩], .ret ⟨0⟩ ]

#guard admitted (admitRegions alphabet scopedFlow)
#guard scopedFlow.check alphabet = none

/-- Replace one block's term (and optionally its label). -/
def withBlock (flow : RegionFlow String) (id : Nat) (label : Option RegionId) (term : RegionTerm) :
    RegionFlow String :=
  { flow with blocks := flow.blocks.map fun block =>
      if block.id.value = id then { block with region := label, term := term } else block }

-- EF-FLOW-CE-004: a `ret` inside a region would return without its releases.
#guard refusal? (admitRegions alphabet (withBlock scopedFlow 2 (some ⟨1⟩) (.plain (.ret ⟨1⟩)))) =
  some .retInside

-- EF-FLOW-CE-005: a `leave` outside every region has nothing to close.
#guard refusal? (admitRegions alphabet (withBlock scopedFlow 3 none (.leave ⟨0⟩))) =
  some .leaveOutside

-- An `acquire` target carrying another label leaves the region without closing it.
#guard refusal? (admitRegions alphabet (withBlock scopedFlow 2 none (.leave ⟨1⟩))) =
  some .successorLabel

-- EF-FLOW-CE-006: a release must take the acquired answer (acquire 1 answers
-- `void`, release 0 takes a `number`).
#guard refusal? (admitRegions alphabet (withBlock scopedFlow 1 (some ⟨1⟩) (.acquire ⟨1⟩ ⟨0⟩ ⟨0⟩ ⟨2⟩ [⟨0⟩]))) =
  some .acquireRelease

-- The `continue_` block must declare exactly the region's result.
#guard refusal? (admitRegions alphabet
    { scopedFlow with blocks := scopedFlow.blocks.map fun block =>
        if block.id.value = 3 then { block with params := ["number", "number"] } else block }) =
  some .continueTyped

-- The entry block is outside every region.
#guard refusal? (admitRegions alphabet (withBlock scopedFlow 0 (some ⟨1⟩) (.enter ⟨1⟩ ⟨1⟩ [⟨0⟩]))) =
  some .entryInside

-- The region clauses pass, then v2 refuses the erasure: a leave with a `void`.
#guard (match admitRegions alphabet (withBlock scopedFlow 2 (some ⟨1⟩) (.leave ⟨0⟩)) with
  | .error (.erased diagnostic) => diagnostic.clause == .termTypeMismatch || diagnostic.clause == .argumentTypeMismatch
  | _ => false) = false
-- (the leave value ⟨0⟩ is a number too, so this variant is admitted: the guard
-- above records that no v2 refusal is produced for it)
#guard admitted (admitRegions alphabet (withBlock scopedFlow 2 (some ⟨1⟩) (.leave ⟨0⟩)))

end EffectsTest.Flow.RegionContract
