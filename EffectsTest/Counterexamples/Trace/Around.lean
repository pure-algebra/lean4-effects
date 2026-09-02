import Effects.Trace
import Effects.Transport
import EffectsTest.Family.TowerSmoke

/-!
# Trace attacks

Witnesses for `EF-TRACE-CE-001` through `EF-TRACE-CE-003` in
`test/counterexamples/REGISTER.md`; attack shapes in
`test/counterexamples/trace/ATTACKS.md`.
-/

namespace EffectsTest.Counterexamples.Trace

open Effects Effects.Trace EffectsTest.Family

abbrev CellEvent := Event CellName Val Unit Unit

/-- `EF-TRACE-CE-001`. `StateT.lift` is a monad homomorphism, so a "tracing"
handler built with `Handler.mapHom` is available; it records nothing. -/
def liftHom (σ : Type) : MonadHom (StateT Nat Id) (StateT σ (StateT Nat Id)) where
  app := StateT.lift
  app_pure a := by
    funext s
    simp [StateT.lift, StateT.run, pure_bind]
    rfl
  app_bind m k := by
    funext s
    simp [StateT.lift, StateT.run, bind_assoc, pure_bind]
    rfl

def liftedCell : Handler CellSig (StateT (List CellEvent) (StateT Nat Id)) :=
  cellService.toHandler.mapHom (liftHom (List CellEvent))

/-- The homomorphism-lifted handler computes the right answer and logs nothing. -/
theorem mapHom_logs_nothing :
    (((interpret liftedCell incr).run []).run 41 : (Nat × List CellEvent) × Nat) =
      ((42, []), 42) := rfl

/-- `EF-TRACE-CE-002`. Two services that answer differently produce equal
operation-only traces and equal outcomes; only the `answer` rows separate
them, so `m1` must keep answers. -/
def cellParam : (name : CellName) → Cell.Param name → Val := fun name =>
  match name with
  | CellName.get => fun _ => Val.unit
  | CellName.put => fun n => Val.nat n

def cellAnswer : (name : CellName) → Cell.Answer name → Val := fun name =>
  match name with
  | CellName.get => fun n => Val.nat n
  | CellName.put => fun _ => Val.unit

def constCell (value : Nat) : Cell.Service Id := fun name =>
  match name with
  | CellName.get => fun _ => value
  | CellName.put => fun _ => ()

def readOnce : Program CellSig Unit :=
  Cell.perform CellName.get () >>= fun _ => Program.pure ()

def traceOf (value : Nat) : List CellEvent :=
  let result : Unit × List CellEvent :=
    (interpret ((constCell value).traced (δ := Unit) (ρ := Unit) id cellParam cellAnswer).toHandler
      readOnce).run []
  result.2

def opsOnly : Mask :=
  { ops := true, answers := false, decisions := false, regions := false,
    finalizers := false, outcome := true, frontier := true }

theorem answers_separate_what_ops_do_not :
    project opsOnly (traceOf 41) = project opsOnly (traceOf 5) ∧
      project Mask.m1 (traceOf 41) ≠ project Mask.m1 (traceOf 5) := by
  decide

/-- `EF-TRACE-CE-003`. Two traces that agree under `m1` and differ unprojected:
agreement is only ever a statement under a named mask. -/
def bare : List CellEvent := [ .op CellName.get .unit, .answer CellName.get (.nat 41), .done (.success .unit) ]
def decided : List CellEvent :=
  [ .decide () true, .op CellName.get .unit, .answer CellName.get (.nat 41), .done (.success .unit) ]

theorem agreement_is_per_mask :
    project Mask.m1 bare = project Mask.m1 decided ∧ bare ≠ decided ∧
      project Mask.m2 bare ≠ project Mask.m2 decided := by
  decide

end EffectsTest.Counterexamples.Trace
