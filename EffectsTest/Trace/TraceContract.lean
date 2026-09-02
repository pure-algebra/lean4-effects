/-
Contract packet: `test/contracts/trace.contract.md`

Frozen surface of the shared service-level trace alphabet. Names, universes,
argument roles, constructor fields and theorem propositions are frozen by the
ascriptions below; binder names may differ.
-/

import Effects.Trace
import EffectsTest.Family.TowerSmoke

namespace EffectsTest.Trace.TraceContract

open Effects
open Effects.Trace

universe u t

section SurfaceSnapshot

variable (ω υ δ ρ : Type u)

#check (@Event.op : {ω υ δ ρ : Type u} → ω → υ → Event ω υ δ ρ)
#check (@Event.answer : {ω υ δ ρ : Type u} → ω → υ → Event ω υ δ ρ)
#check (@Event.failed : {ω υ δ ρ : Type u} → ω → υ → Event ω υ δ ρ)
#check (@Event.decide : {ω υ δ ρ : Type u} → δ → Bool → Event ω υ δ ρ)
#check (@Event.enter : {ω υ δ ρ : Type u} → ρ → Event ω υ δ ρ)
#check (@Event.leave : {ω υ δ ρ : Type u} → ρ → Outcome υ → Event ω υ δ ρ)
#check (@Event.finalizer : {ω υ δ ρ : Type u} → ρ → Outcome υ → Event ω υ δ ρ)
#check (@Event.done : {ω υ δ ρ : Type u} → Outcome υ → Event ω υ δ ρ)
#check (@Event.frontier : {ω υ δ ρ : Type u} → Event ω υ δ ρ)

#check (@Outcome.success : {υ : Type u} → υ → Outcome υ)
#check (@Outcome.failure : {υ : Type u} → υ → Outcome υ)
#check (@Outcome.interrupted : {υ : Type u} → Outcome υ)

#check (@Mask.mk : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Mask)
#check (@Mask.keeps : {ω υ δ ρ : Type u} → Mask → Event ω υ δ ρ → Bool)
#check (@Mask.outcomeOnly : Mask)
#check (@Mask.m1 : Mask)
#check (@Mask.m2 : Mask)
#check (@project : {ω υ δ ρ : Type u} → Mask → List (Event ω υ δ ρ) → List (Event ω υ δ ρ))

#check (@project_project : ∀ {ω υ δ ρ : Type u} (mask : Mask) (trace : List (Event ω υ δ ρ)),
  project mask (project mask trace) = project mask trace)
#check (@project_m2 : ∀ {ω υ δ ρ : Type u} (trace : List (Event ω υ δ ρ)),
  project Mask.m2 trace = trace)
#check (@agree_of_agree_m2 : ∀ {ω υ δ ρ : Type u} {left right : List (Event ω υ δ ρ)},
  project Mask.m2 left = project Mask.m2 right → project Mask.m1 left = project Mask.m1 right)

#check (@Family.Service.traced :
  ∀ {F : Family} {M : Type → Type t} [Monad M] {ω υ δ ρ : Type},
    (F.Name → ω) → ((name : F.Name) → F.Param name → υ) →
    ((name : F.Name) → F.Answer name → υ) →
    F.Service M → F.Service (StateT (List (Event ω υ δ ρ)) M))

#check (@Handler.Projects :
  ∀ {S : Signature} {σ : Type} {M : Type → Type t} [Monad M],
    Handler S (StateT σ M) → Handler S M → Prop)

#check (@interpret_projects_fst :
  ∀ {S : Signature} {σ : Type} {M : Type → Type t} [Monad M] [LawfulMonad M]
    {traced : Handler S (StateT σ M)} {plain : Handler S M},
    traced.Projects plain → ∀ {A : Type} (program : Program S A) (state : σ),
      (fun result => result.1) <$> (interpret traced program).run state = interpret plain program)

#check (@Family.Service.interpret_traced_fst :
  ∀ {F : Family} {M : Type → Type t} [Monad M] [LawfulMonad M] {ω υ δ ρ : Type}
    (nameOf : F.Name → ω) (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ) (service : F.Service M)
    {A : Type} (program : Program F.toSignature A) (log : List (Event ω υ δ ρ)),
    (fun result => result.1) <$>
        (interpret (service.traced nameOf encodeParam encodeAnswer).toHandler program).run log =
      interpret service.toHandler program)

end SurfaceSnapshot

/-! ## Executable receipts on the smoke tower -/

open EffectsTest.Family

/-- Operation names for the smoke family. -/
def cellName : CellName → CellName := id

def cellParam : (name : CellName) → Cell.Param name → Val := fun name =>
  match name with
  | CellName.get => fun _ => Val.unit
  | CellName.put => fun n => Val.nat n

def cellAnswer : (name : CellName) → Cell.Answer name → Val := fun name =>
  match name with
  | CellName.get => fun n => Val.nat n
  | CellName.put => fun _ => Val.unit

abbrev CellEvent := Event CellName Val Unit Unit

abbrev tracedCell : Cell.Service (StateT (List CellEvent) (StateT Nat Id)) :=
  cellService.traced (δ := Unit) (ρ := Unit) cellName cellParam cellAnswer

/-- The traced run of `incr` from cell 41, as a first-order value. -/
def receipt : (Nat × List CellEvent) × Nat :=
  ((interpret tracedCell.toHandler incr).run []).run 41

/-- Answer 42, cell 42, six events. -/
example :
    receipt =
      ((42,
        [ .op CellName.get .unit, .answer CellName.get (.nat 41)
        , .op CellName.put (.nat 42), .answer CellName.put .unit
        , .op CellName.get .unit, .answer CellName.get (.nat 42) ]), 42) := by
  decide

/-- The projection law, instantiated on the smoke tower. -/
example := Family.Service.interpret_traced_fst (δ := Unit) (ρ := Unit)
  cellName cellParam cellAnswer cellService incr []

/-- Masks are projections: `m1` drops nothing from a trace with only operations
and answers, and `outcomeOnly` drops everything in it. -/
example :
    project Mask.m1 ([ .op CellName.get .unit, .answer CellName.get (.nat 41) ] : List CellEvent) =
      [ .op CellName.get .unit, .answer CellName.get (.nat 41) ] := by decide

example :
    project Mask.outcomeOnly
      ([ .op CellName.get .unit, .answer CellName.get (.nat 41), .done (.success (.nat 41)) ]
        : List CellEvent) =
      [ .done (.success (.nat 41)) ] := by decide

end EffectsTest.Trace.TraceContract
