import Effects.Algebra.Laws

/-!
# `E4-ALG-CE-006`: a fixed-fuel evaluator admits no composition law

Local re-derivation, in slice S3 of the split, of the Foldlab witness
`run_has_no_composition_law` (`library/cas/Cas/Backend/Universal.lean:894–910`
at commit `feb29321fd50204aa338209d313e84a3f8b71c66`, Apache-2.0). Foldlab's
witness lives over its CAS word store; this one is generic: a one-operation
signature, an idempotent state handler, and an evaluator that stops after a
fixed number of operations.

Two programs with the same fuel-2 result (one `set` and two `set`s) have
different fuel-2 results after the same continuation, so no function of the
parts' results can be the whole's result. Composition is stated at
`Effects.interpret`, never at one fixed fuel.
-/

namespace EffectsTest.Counterexamples.Algebra.FixedFuel

open Effects

def OneSig : Signature.{0, 0} where
  Op := Unit
  Answer := fun _ => Unit

abbrev Store := StateT Nat Id

/-- Idempotent: sets the store to `1` however often it runs. -/
def setOne : Handler OneSig Store := ⟨fun _ => modify fun _ => 1⟩

/-- Evaluate at most `fuel` operations; `none` when the fuel runs out first. -/
def run (handler : Handler OneSig Store) :
    Nat → Program OneSig A → Nat → Option A × Nat
  | _, .pure value, store => (some value, store)
  | 0, .vis _ _, store => (none, store)
  | fuel + 1, .vis operation next, store =>
      match handler.handle operation store with
      | (answer, store') => run handler fuel (next answer) store'

def once : Program OneSig Unit := Program.perform ()

def twice : Program OneSig Unit := once >>= fun _ => once

/-- `once` and `twice` are indistinguishable at fuel 2. -/
theorem run_once_eq_run_twice :
    (fun store => run setOne 2 once store) = fun store => run setOne 2 twice store :=
  funext fun _ => rfl

/-- **Falsifier.** No `comp` reconstructs the fuel-2 result of `p >>= f` from
the fuel-2 results of `p` and `f`. -/
theorem run_has_no_composition_law :
    ¬ ∃ comp : (Nat → Option Unit × Nat) → (Unit → Nat → Option Unit × Nat) →
        (Nat → Option Unit × Nat),
      ∀ (program : Program OneSig Unit) (next : Unit → Program OneSig Unit),
        (fun store => run setOne 2 (program >>= next) store) =
          comp (fun store => run setOne 2 program store)
            (fun answer store => run setOne 2 (next answer) store) := by
  intro ⟨comp, law⟩
  have first := law once fun _ => once
  have second := law twice fun _ => once
  have parts := congrArg
    (fun parts => comp parts fun (_ : Unit) store => run setOne 2 once store)
    run_once_eq_run_twice
  have whole := first.trans (parts.trans second.symm)
  have at0 := congrArg Prod.fst (congrFun whole 0)
  exact nomatch at0

end EffectsTest.Counterexamples.Algebra.FixedFuel
