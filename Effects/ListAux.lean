import Std

/-!
# List auxiliaries proved by induction

Two counting facts about duplicate-free lists, used by the flow layer's
reachability measure and by any consumer that needs the same pigeonhole.

They exist as their own module because they are proved *by induction* rather
than taken from a library: the flow layer's axiom ceiling is `propext` and
`Quot.sound`, and the corresponding `List` lemmas in the standard library
reach `Classical.choice`. Publishing them is finding #39 of the 2026-09-03
survey: `Effects` used to hide this pair and export the saturation
scaffolding whose only purpose is to reach it, which is backwards. Both are
generic in `α`; the flow layer instantiates them at `BlockId`.
-/

namespace Effects.ListAux

universe u

variable {α : Type u} [DecidableEq α]

/-- Removing every copy of a present element shortens a list. -/
theorem length_filter_ne {a : α} :
    ∀ {l : List α}, a ∈ l →
      (l.filter fun x => decide (x ≠ a)).length + 1 ≤ l.length
  | [], mem => absurd mem List.not_mem_nil
  | b :: bs, mem => by
      by_cases eq : b = a
      · subst eq
        rw [List.filter_cons_of_neg (p := fun x => decide (x ≠ b))
          (by rw [decide_eq_false (fun h => h rfl)]; exact Bool.false_ne_true)]
        rw [List.length_cons]
        exact Nat.succ_le_succ (List.length_filter_le _ _)
      · rw [List.filter_cons_of_pos (p := fun x => decide (x ≠ a)) (decide_eq_true eq),
          List.length_cons, List.length_cons]
        have tailMem : a ∈ bs := by
          rcases List.mem_cons.mp mem with h | h
          · exact absurd h.symm eq
          · exact h
        have ih := length_filter_ne tailMem
        omega

/-- A duplicate-free list is no longer than any list containing it. -/
theorem length_le_of_nodup_subset :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, l₂, nodup, sub => by
      have ⟨notMem, nodupTail⟩ := List.nodup_cons.mp nodup
      have aMem : a ∈ l₂ := sub List.mem_cons_self
      have tailSub : l ⊆ l₂.filter fun x => decide (x ≠ a) := by
        intro x hx
        have ne : x ≠ a := fun eq => notMem (eq ▸ hx)
        exact List.mem_filter.mpr ⟨sub (List.mem_cons_of_mem _ hx), decide_eq_true ne⟩
      have ih := length_le_of_nodup_subset nodupTail tailSub
      have bound := length_filter_ne aMem
      rw [List.length_cons]
      omega

end Effects.ListAux
