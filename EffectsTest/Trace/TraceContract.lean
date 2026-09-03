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

universe u v t

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
#check (@Outcome.defect : {υ : Type u} → υ → Outcome υ)
#check (@Outcome.interrupted : {υ : Type u} → Outcome υ)

-- v0.6.0. `Outcome.map` re-encodes the payload with no `ToVal` in sight; the
-- payload universes are independent.
#check (@Outcome.map : {υ : Type u} → {ν : Type v} → (υ → ν) → Outcome υ → Outcome ν)
#check (@Outcome.map_id : ∀ {υ : Type u} (outcome : Outcome υ), outcome.map id = outcome)
#check (@Outcome.map_comp : ∀ {υ : Type u} {ν : Type v} {ξ : Type u}
  (second : ν → ξ) (first : υ → ν) (outcome : Outcome υ),
  (outcome.map first).map second = outcome.map (second ∘ first))

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

#check (@Family.Service.tracedExcept :
  ∀ {F : Family} {ε : Type} {M : Type → Type t} [Monad M] {ω υ δ ρ : Type},
    (F.Name → ω) → ((name : F.Name) → F.Param name → υ) →
    ((name : F.Name) → F.Answer name → υ) → (ε → υ) →
    F.Service (ExceptT ε M) → F.Service (ExceptT ε (StateT (List (Event ω υ δ ρ)) M)))

#check (@Family.Service.interpret_tracedExcept_fst :
  ∀ {F : Family} {ε : Type} {M : Type → Type t} [Monad M] [LawfulMonad M] {ω υ δ ρ : Type}
    (nameOf : F.Name → ω) (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ) (encodeError : ε → υ)
    (service : F.Service (ExceptT ε M)) {A : Type} (program : Program F.toSignature A)
    (log : List (Event ω υ δ ρ)),
    (fun result => result.1) <$>
        ((interpret (service.tracedExcept nameOf encodeParam encodeAnswer encodeError).toHandler
          program).run.run log) =
      (interpret service.toHandler program).run)

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

/-! ## v0.6.0 receipts: the new constructor and the mask's blindness to it -/

/-- A defect is not a failure carrying the same payload. -/
example : (Outcome.defect (Val.str "boom") : Outcome Val) ≠ .failure (.str "boom") := by decide

/-- Nor is it a success or an interruption. -/
example :
    (Outcome.defect (Val.str "boom") : Outcome Val) ≠ .success (.str "boom") ∧
      (Outcome.defect (Val.str "boom") : Outcome Val) ≠ .interrupted := by decide

/-- `Mask.keeps` decides on the event's kind, so it cannot see which outcome a
`done`, a `leave` or a `finalizer` carries: the four outcomes are kept and
dropped together under every mask in the packet. -/
example :
    ([Mask.outcomeOnly, Mask.m1, Mask.m2].all fun mask =>
      ([ Outcome.success Val.unit, .failure .unit, .defect .unit, .interrupted ]
          : List (Outcome Val)).all fun outcome =>
        (mask.keeps (Event.done outcome : CellEvent) ==
            mask.keeps (Event.done (Outcome.success Val.unit) : CellEvent) &&
          mask.keeps (Event.leave () outcome : CellEvent) ==
            mask.keeps (Event.leave () (Outcome.success Val.unit) : CellEvent) &&
          mask.keeps (Event.finalizer () outcome : CellEvent) ==
            mask.keeps (Event.finalizer () (Outcome.success Val.unit) : CellEvent)))
      = true := by decide

/-- The projection laws hold on a trace that carries a defect: `m2` keeps it,
`m1` and `outcomeOnly` keep the `done` row it annotates, and projecting twice
is projecting once. -/
def defectTrace : List CellEvent :=
  [ .op CellName.get .unit, .answer CellName.get (.nat 41)
  , .decide () true, .enter (), .finalizer () (.defect (.str "boom"))
  , .leave () (.defect (.str "boom")), .done (.defect (.str "boom")) ]

example : project Mask.m2 defectTrace = defectTrace := by decide

example : project Mask.m2 (project Mask.m2 defectTrace) = project Mask.m2 defectTrace := by decide

example : project Mask.m1 (project Mask.m2 defectTrace) = project Mask.m1 defectTrace := by decide

example :
    project Mask.outcomeOnly defectTrace = [ .done (.defect (.str "boom")) ] := by decide

/-- `Outcome.map` moves a payload along an encoding, constructor by
constructor. -/
example :
    ([ Outcome.success 41, .failure 7, .defect 9, .interrupted ].map
      (Outcome.map (fun n : Nat => Val.nat n)))
      = [ .success (.nat 41), .failure (.nat 7), .defect (.nat 9), .interrupted ] := by decide

/-- `map_id` and `map_comp`, instantiated. -/
example : (Outcome.defect (Val.str "boom")).map id = Outcome.defect (Val.str "boom") :=
  Outcome.map_id _

example :
    ((Outcome.defect (7 : Nat)).map (fun n => n + 1)).map (fun n : Nat => Val.nat n) =
      (Outcome.defect (7 : Nat)).map ((fun n : Nat => Val.nat n) ∘ (fun n => n + 1)) :=
  Outcome.map_comp _ _ _

end EffectsTest.Trace.TraceContract
