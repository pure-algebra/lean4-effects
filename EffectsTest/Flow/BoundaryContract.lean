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

end EffectsTest.Flow.BoundaryContract
