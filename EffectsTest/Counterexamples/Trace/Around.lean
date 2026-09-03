import Effects.Trace
import Effects.Experimental.Transport
import EffectsTest.Family.TowerSmoke

/-!
# Trace attacks

Witnesses for `EF-TRACE-CE-001` through `EF-TRACE-CE-004` in
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

/-! ## `EF-TRACE-CE-004` — a defect rendered as a failure

The v0.5.0 alphabet had no `defect`, so every face that met a host `Die` had to
choose an existing constructor. Choosing `failure` is the collapse this row
freezes: it is exactly what the rc.112 tracer did, rendering a die as
`{"failure":[]}`, byte-identical to a unit failure. The collapse is stated here
as an endomorphism of the alphabet, so no `String` is traversed and the row
stands without a renderer. -/

/-- The v0.5.0 choice: report a defect as a failure with the same payload. -/
def squashDefect : Outcome Val → Outcome Val
  | .defect error => .failure error
  | other => other

/-- Lifted to an event: only the outcome an event carries is rewritten. -/
def squashEvent : CellEvent → CellEvent
  | .done outcome => .done (squashDefect outcome)
  | .leave region outcome => .leave region (squashDefect outcome)
  | .finalizer region outcome => .finalizer region (squashDefect outcome)
  | other => other

def died : List CellEvent :=
  [ .op CellName.get .unit, .answer CellName.get (.nat 41), .done (.defect (.str "boom")) ]

def failed : List CellEvent :=
  [ .op CellName.get .unit, .answer CellName.get (.nat 41), .done (.failure (.str "boom")) ]

/-- `EF-TRACE-CE-004`. A defect and a failure carrying the same payload become
one trace under the collapse, and they do so under *every* mask in the packet,
`outcomeOnly` included: no projection can recover the distinction, because a
mask sees an event's kind and never the outcome it carries. The two traces are
distinct in the v0.6.0 alphabet, so the collapse loses information that the
alphabet holds. -/
theorem a_defect_rendered_as_a_failure :
    died.map squashEvent = failed.map squashEvent ∧
      died ≠ failed ∧
      ([Mask.outcomeOnly, Mask.m1, Mask.m2].all fun mask =>
        project mask died != project mask failed) = true := by
  decide

end EffectsTest.Counterexamples.Trace
