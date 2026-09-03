import Effects.Family
import Effects.Algebra.Laws

/-!
# The shared service-level trace alphabet

One observation vocabulary for every face that executes a program over a
family: the algebra (through `Family.Service.traced`), a first-order flow
runner, and a host. An event names an operation with its request and answer,
a decision site with its answer, a region boundary, a finalizer with the exit
it observed, or the outcome. Nothing here is a host primitive: the seventeen
rc.112 primitives are not events of this alphabet, and no `String` is
traversed in this module (rendering lives in a consumer).

Masks are projections: `project mask` is a filter, `m1` keeps operations,
answers, failures and the outcome, `m2` keeps everything. Agreement between two
emitters is always stated under a named mask. A mask decides on an event's
*kind* alone, so widening `Outcome` leaves `Mask.keeps` and every projection
law untouched (v0.6.0: `Outcome.defect` is kept exactly where the outcome it
annotates was already kept).

An outcome is `success`, `failure`, `defect` or `interrupted`. This library
produces only the first two: the traced services emit `op`, `answer` and
`failed` rows, and their `done`/`leave`/`finalizer` outcomes are supplied by a
caller. `defect` and `interrupted` are here so that a downstream runner or a
host bridge has a place to land, and they carry no law in this module.

The one law is `Family.Service.interpret_traced_fst`: forgetting the log of a
traced service recovers the plain interpretation. It is an around-wrapper, not a
monad homomorphism; `Handler.mapHom` of a lift logs nothing.
-/

namespace Effects

universe u v w n p a t uS uAns uTarget

namespace Trace

/-- First-order wire values. Lists encode as right-nested pairs closed by
`unit`; `Except` encodes as `pair (bool ok) payload`. -/
inductive Val : Type
  | unit
  | nat (n : Nat)
  | int (i : Int)
  | bool (b : Bool)
  | str (s : String)
  | pair (left right : Val)
  | none
  | some (value : Val)
deriving DecidableEq, Repr, Inhabited

/-- Encode a value on the wire. -/
class ToVal (α : Type u) where
  toVal : α → Val

variable {α : Type u} {β : Type v} {ε : Type w}

instance : ToVal Unit := ⟨fun _ => .unit⟩
instance : ToVal Nat := ⟨.nat⟩
instance : ToVal Int := ⟨.int⟩
instance : ToVal Bool := ⟨.bool⟩
instance : ToVal String := ⟨.str⟩
instance : ToVal Val := ⟨id⟩
instance [ToVal α] [ToVal β] : ToVal (α × β) := ⟨fun p => .pair (ToVal.toVal p.1) (ToVal.toVal p.2)⟩
instance [ToVal α] : ToVal (Option α) :=
  ⟨fun | Option.none => .none | Option.some a => .some (ToVal.toVal a)⟩
instance [ToVal α] : ToVal (List α) :=
  ⟨fun xs => xs.foldr (fun a acc => .pair (ToVal.toVal a) acc) .unit⟩
instance [ToVal ε] [ToVal α] : ToVal (Except ε α) :=
  ⟨fun | .error e => .pair (.bool false) (ToVal.toVal e) | .ok a => .pair (.bool true) (ToVal.toVal a)⟩

/-- How a program, a region body, or a finalizer ended. `failure` is the
typed, recoverable error of the program's own error channel; `defect` is a
host defect (an rc.112 `Die`), a distinct constructor because a defect that
renders as a failure is indistinguishable from a failure carrying the same
payload (`EF-TRACE-CE-004`). Neither `defect` nor `interrupted` has a producer
in this library: `Family.Service.traced` and `Family.Service.tracedExcept`
emit only `op`, `answer` and `failed`, and the two constructors exist for
runners and bridges downstream to land in. -/
inductive Outcome (υ : Type u) : Type u
  | success (value : υ)
  | failure (error : υ)
  | defect (error : υ)
  | interrupted
deriving DecidableEq, Repr

namespace Outcome

/-- Re-encode the payload of an outcome. No `ToVal` is involved: the payload
universe is arbitrary, and the frame-simulation projection needs to move an
outcome along a payload encoding without committing to a wire form. -/
def map {υ : Type u} {ν : Type v} (encode : υ → ν) : Outcome υ → Outcome ν
  | .success value => .success (encode value)
  | .failure error => .failure (encode error)
  | .defect error => .defect (encode error)
  | .interrupted => .interrupted

@[simp] theorem map_id {υ : Type u} (outcome : Outcome υ) : outcome.map id = outcome := by
  cases outcome <;> rfl

theorem map_comp {υ : Type u} {ν : Type v} {ξ : Type w}
    (second : ν → ξ) (first : υ → ν) (outcome : Outcome υ) :
    (outcome.map first).map second = outcome.map (second ∘ first) := by
  cases outcome <;> rfl

end Outcome

/-- One observation. `ω` names operations, `υ` carries values, `δ` names
decision sites, `ρ` names regions. -/
inductive Event (ω υ δ ρ : Type u) : Type u
  | op (name : ω) (request : υ)
  | answer (name : ω) (value : υ)
  | failed (name : ω) (error : υ)
  | decide (site : δ) (branch : Bool)
  | enter (region : ρ)
  | leave (region : ρ) (outcome : Outcome υ)
  | finalizer (region : ρ) (outcome : Outcome υ)
  | done (outcome : Outcome υ)
  | frontier
deriving DecidableEq, Repr

/-- A mask says which event kinds survive comparison. It is a projection. -/
structure Mask where
  ops : Bool
  answers : Bool
  decisions : Bool
  regions : Bool
  finalizers : Bool
  outcome : Bool
  frontier : Bool
deriving DecidableEq, Repr

variable {ω υ δ ρ : Type u}

namespace Mask

def keeps (mask : Mask) : Event ω υ δ ρ → Bool
  | .op .. => mask.ops
  | .answer .. => mask.answers
  | .failed .. => mask.answers
  | .decide .. => mask.decisions
  | .enter .. => mask.regions
  | .leave .. => mask.regions
  | .finalizer .. => mask.finalizers
  | .done .. => mask.outcome
  | .frontier => mask.frontier

/-- Only how the program ended. -/
def outcomeOnly : Mask :=
  { ops := false, answers := false, decisions := false, regions := false,
    finalizers := false, outcome := true, frontier := true }

/-- Operations, their answers and failures, and the outcome. -/
def m1 : Mask :=
  { ops := true, answers := true, decisions := false, regions := false,
    finalizers := false, outcome := true, frontier := true }

/-- Everything: decisions, regions and finalizers too. -/
def m2 : Mask :=
  { ops := true, answers := true, decisions := true, regions := true,
    finalizers := true, outcome := true, frontier := true }

theorem m2_keeps (event : Event ω υ δ ρ) : m2.keeps event = true := by
  cases event <;> rfl

end Mask

/-- Project a trace onto a mask. -/
def project (mask : Mask) (trace : List (Event ω υ δ ρ)) : List (Event ω υ δ ρ) :=
  trace.filter mask.keeps

theorem project_nil (mask : Mask) : project mask ([] : List (Event ω υ δ ρ)) = [] := rfl

theorem project_cons (mask : Mask) (event : Event ω υ δ ρ) (rest : List (Event ω υ δ ρ)) :
    project mask (event :: rest) =
      if mask.keeps event then event :: project mask rest else project mask rest := by
  simp [project, List.filter_cons]

/-- Projecting twice is projecting once. -/
theorem project_project (mask : Mask) (trace : List (Event ω υ δ ρ)) :
    project mask (project mask trace) = project mask trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      by_cases keep : mask.keeps event = true
      · simp [project_cons, keep, ih]
      · simp [project_cons, keep, ih]

/-- `m2` keeps everything. -/
theorem project_m2 (trace : List (Event ω υ δ ρ)) : project Mask.m2 trace = trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih => simp [project_cons, Mask.m2_keeps, ih]

/-- `m1` refines `m2`: agreement under `m2` implies agreement under `m1`. -/
theorem project_m1_m2 (trace : List (Event ω υ δ ρ)) :
    project Mask.m1 (project Mask.m2 trace) = project Mask.m1 trace := by
  rw [project_m2]

theorem agree_of_agree_m2 {left right : List (Event ω υ δ ρ)}
    (agree : project Mask.m2 left = project Mask.m2 right) :
    project Mask.m1 left = project Mask.m1 right := by
  rw [← project_m1_m2 left, ← project_m1_m2 right, agree]

end Trace

/-! ## Tracing a service -/

namespace Family

/-- Wrap every method of a service so that its request and answer are
recorded. The log is threaded as state; the underlying method runs in `M`. -/
def Service.traced {F : Family.{n, p, a}} {M : Type a → Type t} [Monad M]
    {ω υ δ ρ : Type a}
    (nameOf : F.Name → ω)
    (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ)
    (service : F.Service M) :
    F.Service (StateT (List (Trace.Event ω υ δ ρ)) M) :=
  fun name param log =>
    service name param >>= fun answer =>
      pure (answer,
        log ++ [Trace.Event.op (nameOf name) (encodeParam name param),
                Trace.Event.answer (nameOf name) (encodeAnswer name answer)])

end Family

/-- A handler into `StateT σ M` projects onto a handler into `M` when forgetting
the state recovers every method. -/
def Handler.Projects {S : Signature.{uS, uAns}} {σ : Type uAns}
    {M : Type uAns → Type t} [Monad M]
    (traced : Handler S (StateT σ M)) (plain : Handler S M) : Prop :=
  ∀ (operation : S.Op) (state : σ),
    (fun result => result.1) <$> (traced.handle operation).run state = plain.handle operation

/-- Forgetting the state of a projecting handler recovers the plain
interpretation. One induction on the program, generalised over the state. -/
theorem interpret_projects_fst {S : Signature.{uS, uAns}} {σ : Type uAns}
    {M : Type uAns → Type t} [Monad M] [LawfulMonad M]
    {traced : Handler S (StateT σ M)} {plain : Handler S M}
    (projects : traced.Projects plain) {A : Type uAns}
    (program : Program S A) (state : σ) :
    (fun result => result.1) <$> (interpret traced program).run state =
      interpret plain program := by
  induction program generalizing state with
  | pure value =>
      show (fun result => result.1) <$> (pure (value, state) : M (A × σ)) = pure value
      rw [map_pure]
  | vis operation next ih =>
      show (fun result => result.1) <$>
          ((traced.handle operation).run state >>= fun result =>
            (interpret traced (next result.1)).run result.2) =
        plain.handle operation >>= fun answer => interpret plain (next answer)
      rw [map_bind]
      simp only [ih]
      rw [← projects operation state, bind_map_left]

/-- The traced service projects onto the plain service. -/
theorem Family.Service.traced_projects {F : Family.{n, p, a}} {M : Type a → Type t}
    [Monad M] [LawfulMonad M] {ω υ δ ρ : Type a}
    (nameOf : F.Name → ω)
    (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ)
    (service : F.Service M) :
    (service.traced (δ := δ) (ρ := ρ) nameOf encodeParam encodeAnswer).toHandler.Projects
      service.toHandler := by
  intro operation log
  simp only [Family.Service.toHandler, Family.Service.traced, StateT.run]
  rw [map_bind]
  simp only [map_pure]
  exact bind_pure _

/-- The law: forgetting the log of a traced service recovers the plain
interpretation. -/
theorem Family.Service.interpret_traced_fst {F : Family.{n, p, a}} {M : Type a → Type t}
    [Monad M] [LawfulMonad M] {ω υ δ ρ : Type a}
    (nameOf : F.Name → ω)
    (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ)
    (service : F.Service M) {A : Type a}
    (program : Program F.toSignature A) (log : List (Trace.Event ω υ δ ρ)) :
    (fun result => result.1) <$>
        (interpret (service.traced nameOf encodeParam encodeAnswer).toHandler program).run log =
      interpret service.toHandler program :=
  interpret_projects_fst (service.traced_projects nameOf encodeParam encodeAnswer) program log

/-! ## Tracing a fallible service

The aborting error reading: a service into `ExceptT ε M`. The log sits
*outside* the error (`ExceptT ε (StateT log M)`), so a failed operation still
records its request and a `failed` row, and the caller sees both the error and
the log. -/

namespace Family

/-- Wrap every method of a fallible service: request, then `answer` on
success or `failed` on error, re-raising the error. -/
def Service.tracedExcept {F : Family.{n, p, a}} {ε : Type a} {M : Type a → Type t} [Monad M]
    {ω υ δ ρ : Type a}
    (nameOf : F.Name → ω)
    (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ)
    (encodeError : ε → υ)
    (service : F.Service (ExceptT ε M)) :
    F.Service (ExceptT ε (StateT (List (Trace.Event ω υ δ ρ)) M)) :=
  fun name param => ExceptT.mk fun log =>
    (service name param).run >>= fun result =>
      pure (result,
        log ++ [Trace.Event.op (nameOf name) (encodeParam name param)] ++
          match result with
          | .ok answer => [Trace.Event.answer (nameOf name) (encodeAnswer name answer)]
          | .error error => [Trace.Event.failed (nameOf name) (encodeError error)])

end Family

/-- A handler into `ExceptT ε (StateT σ M)` projects onto one into `ExceptT ε M`
when forgetting the state recovers every method. -/
def Handler.ProjectsExcept {S : Signature.{uS, uAns}} {ε σ : Type uAns}
    {M : Type uAns → Type t} [Monad M]
    (traced : Handler S (ExceptT ε (StateT σ M))) (plain : Handler S (ExceptT ε M)) : Prop :=
  ∀ (operation : S.Op) (state : σ),
    (fun result => result.1) <$> ((traced.handle operation).run.run state) =
      (plain.handle operation).run

/-- Forgetting the state of a projecting fallible handler recovers the plain
fallible interpretation. One induction on the program, generalised over the
state; the error branch is where the two carriers agree by `pure`. -/
theorem interpret_projectsExcept_fst {S : Signature.{uS, uAns}} {ε σ : Type uAns}
    {M : Type uAns → Type t} [Monad M] [LawfulMonad M]
    {traced : Handler S (ExceptT ε (StateT σ M))} {plain : Handler S (ExceptT ε M)}
    (projects : traced.ProjectsExcept plain) {A : Type uAns}
    (program : Program S A) (state : σ) :
    (fun result => result.1) <$> ((interpret traced program).run.run state) =
      (interpret plain program).run := by
  induction program generalizing state with
  | pure value =>
      show (fun result => result.1) <$> (pure (Except.ok value, state) : M (Except ε A × σ)) =
        (pure (Except.ok value) : M (Except ε A))
      rw [map_pure]
  | vis operation next ih =>
      rw [interpret_vis, interpret_vis, ExceptT.run_bind, ExceptT.run_bind, StateT.run_bind, map_bind,
        ← projects operation state, bind_map_left]
      refine bind_congr fun result => ?_
      cases outcome : result.1 with
      | ok answer => simp only [ih]
      | error error => simp only [StateT.run_pure, map_pure]

/-- The traced fallible service projects onto the plain one. -/
theorem Family.Service.tracedExcept_projects {F : Family.{n, p, a}} {ε : Type a}
    {M : Type a → Type t} [Monad M] [LawfulMonad M] {ω υ δ ρ : Type a}
    (nameOf : F.Name → ω)
    (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ)
    (encodeError : ε → υ)
    (service : F.Service (ExceptT ε M)) :
    (service.tracedExcept (δ := δ) (ρ := ρ) nameOf encodeParam encodeAnswer encodeError).toHandler.ProjectsExcept
      service.toHandler := by
  intro operation log
  simp only [Family.Service.toHandler, Family.Service.tracedExcept, ExceptT.run, ExceptT.mk, StateT.run]
  rw [map_bind]
  simp only [map_pure]
  exact bind_pure _

/-- The law for the fallible reading: forgetting the log recovers the plain
fallible interpretation, error included. -/
theorem Family.Service.interpret_tracedExcept_fst {F : Family.{n, p, a}} {ε : Type a}
    {M : Type a → Type t} [Monad M] [LawfulMonad M] {ω υ δ ρ : Type a}
    (nameOf : F.Name → ω)
    (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ)
    (encodeError : ε → υ)
    (service : F.Service (ExceptT ε M)) {A : Type a}
    (program : Program F.toSignature A) (log : List (Trace.Event ω υ δ ρ)) :
    (fun result => result.1) <$>
        ((interpret (service.tracedExcept nameOf encodeParam encodeAnswer encodeError).toHandler
          program).run.run log) =
      (interpret service.toHandler program).run :=
  interpret_projectsExcept_fst
    (service.tracedExcept_projects nameOf encodeParam encodeAnswer encodeError) program log

/-- Performing one operation logs exactly its request and its answer. -/
theorem Family.Service.traced_perform {F : Family.{n, p, a}} {M : Type a → Type t}
    [Monad M] [LawfulMonad M] {ω υ δ ρ : Type a}
    (nameOf : F.Name → ω)
    (encodeParam : (name : F.Name) → F.Param name → υ)
    (encodeAnswer : (name : F.Name) → F.Answer name → υ)
    (service : F.Service M) (name : F.Name) (param : F.Param name)
    (log : List (Trace.Event ω υ δ ρ)) :
    (interpret (service.traced nameOf encodeParam encodeAnswer).toHandler
        (F.perform name param)).run log =
      service name param >>= fun answer =>
        pure (answer,
          log ++ [Trace.Event.op (nameOf name) (encodeParam name param),
                  Trace.Event.answer (nameOf name) (encodeAnswer name answer)]) := by
  show ((service.traced nameOf encodeParam encodeAnswer).toHandler.handle ⟨name, param⟩ >>=
      fun answer => (pure answer : StateT _ M _)).run log = _
  rw [bind_pure]
  rfl

end Effects
