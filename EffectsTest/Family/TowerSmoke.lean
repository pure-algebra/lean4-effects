import Effects.Experimental.Morphism
import Effects.Experimental.Transport
import Effects.Family

/-! Executable smoke: the Cell-over-Jobs tower in family form, reduced by `rfl`. -/

namespace EffectsTest.Family
open Effects


inductive TyCode | nat | unit deriving DecidableEq, Repr

abbrev TyCode.denote : TyCode → Type
  | .nat => Nat
  | .unit => Unit

inductive CellName | get | put deriving DecidableEq, Repr

/-- The rows an `effect_signature Cell` would emit: names and type codes only. -/
abbrev cellAlphabet : Alphabet TyCode :=
  ⟨CellName, fun n => match n with | CellName.get => .unit | CellName.put => .nat,
             fun n => match n with | CellName.get => .nat | CellName.put => .unit⟩

abbrev Cell : Family := cellAlphabet.toFamily TyCode.denote
abbrev CellSig := Cell.toSignature

inductive JobsName | schedule deriving DecidableEq, Repr

abbrev jobsAlphabet : Alphabet TyCode :=
  ⟨JobsName, fun _ => .nat, fun _ => .unit⟩

abbrev Jobs : Family := jobsAlphabet.toFamily TyCode.denote
abbrev JobsSig := Jobs.toSignature

/-- A program written against the family. `Cell.perform .put n` is exactly
`yield* cell.put(n)`. -/
def incr : Program CellSig Nat :=
  Cell.perform CellName.get () >>= fun x =>
  Cell.perform CellName.put (x + 1) >>= fun _ =>
  Cell.perform CellName.get ()

/-- The service record, which is the `Layer.effect` body. -/
def cellService : Cell.Service (StateT Nat Id) := fun name =>
  match name with
  | CellName.get => fun _ => get
  | CellName.put => fun n => set n

def jobsService : Jobs.Service (StateT (List Nat) Id) := fun name =>
  match name with
  | JobsName.schedule => fun job => modify (· ++ [job])

/-- Cell implemented over Jobs: every `put` also schedules the value. -/
def cellOverJobs : Cell.Service (StateT Nat (Program JobsSig)) := fun name =>
  match name with
  | CellName.get => fun _ => get
  | CellName.put => fun n => set n >>= fun _ => StateT.lift (Jobs.perform JobsName.schedule n)

/-- `Layer.provide(JobsLive)`: transport the state through the tower. -/
def composite : Handler CellSig (StateT Nat (StateT (List Nat) Id)) :=
  cellOverJobs.toHandler.mapHom ((interpretHom jobsService.toHandler).stateT Nat)

example : ((((interpret composite incr).run 41).run []) : (Nat × Nat) × List Nat) =
    ((42, 42), [42]) := rfl

/-- `Layer.merge`: sum after transport, with the second summand lifted. -/
def liftJobs : Handler JobsSig (StateT Nat (StateT (List Nat) Id)) :=
  ⟨fun operation => StateT.lift (jobsService.toHandler.handle operation)⟩

def full : Handler (CellSig ⊕ₛ JobsSig) (StateT Nat (StateT (List Nat) Id)) :=
  composite.sum liftJobs

/-- The same handler, reindexed for a consumer that spelled the row the other
way round. No new handler is written. -/
def fullFlipped : Handler (JobsSig ⊕ₛ CellSig) (StateT Nat (StateT (List Nat) Id)) :=
  full.pull Signature.Hom.comm

example : ((((interpret fullFlipped
      (Program.map Signature.Hom.inr incr >>= fun n =>
        Program.map Signature.Hom.inl (Jobs.perform JobsName.schedule (n * 10)) >>= fun _ =>
        Program.pure n)).run 0).run []) : (Nat × Nat) × List Nat) =
    ((1, 1), [1, 10]) := rfl

end EffectsTest.Family
