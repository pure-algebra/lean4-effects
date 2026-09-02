import Effects.Algebra.Universal

/-!
# `E4-ALG-CE-002` and `E4-ALG-CE-003`: neither half of the interpreter pin is enough

Local re-derivation, in slice S3 of the split, of the two Foldlab witnesses
`pinned_needs_op_agreement` and `pinned_needs_the_morphism_law`
(`library/cas/Cas/Backend/Universal.lean:701–727` at commit
`feb29321fd50204aa338209d313e84a3f8b71c66`, Apache-2.0). The attack is the
same; the carrier is `Effects` over a one-operation signature and a counter
state.

* An operator that is a monad morphism at every handler but ignores the
  handler it is given: pure/bind preservation alone does not pin it.
* An operator that agrees with every handler on every single operation but
  drifts on the second: operation agreement alone does not pin it either.

Only the conjunction, as `Effects.interpret_pinned` requires, does.
-/

namespace EffectsTest.Counterexamples.Algebra.InterpreterPin

open Effects

/-- One operation whose answer is `Unit`. -/
def OneSig : Signature.{0, 0} where
  Op := Unit
  Answer := fun _ => Unit

/-- The target: a counter threaded through `StateT`. -/
abbrev Counter := StateT Nat Id

/-- The handler that does nothing. -/
def nop : Handler OneSig Counter := ⟨fun _ => pure ()⟩

/-- The handler that increments the counter. -/
def tick : Handler OneSig Counter := ⟨fun _ => modify fun n => n + 1⟩

/-- Two operations in sequence. -/
def twoOps : Program OneSig Unit :=
  Program.perform () >>= fun _ => Program.perform ()

/-- `E4-ALG-CE-002`: ignores the handler it is handed. -/
def ignores (_handler : Handler OneSig Counter) :
    {A : Type} → Program OneSig A → Counter A :=
  fun program => interpret nop program

/-- **Falsifier for the operation-agreement half.** `ignores h` is a monad
morphism for every `h`, and still disagrees with `interpret tick` on one
operation. -/
theorem morphism_alone_does_not_pin :
    (∀ handler : Handler OneSig Counter,
      IsMonadMorphism OneSig (fun {_A} program => ignores handler program)) ∧
    ignores tick (Program.perform ()) ≠ interpret tick (Program.perform ()) := by
  refine ⟨fun _ => interpret_isMonadMorphism nop, ?_⟩
  intro h
  have h0 : (((), 0) : Unit × Nat) = ((), 1) := congrFun h 0
  exact absurd (congrArg Prod.snd h0) (by decide)

/-- `E4-ALG-CE-003`: uses the given handler for the first operation and
`tick` for every later one. -/
def drifts (handler : Handler OneSig Counter) :
    {A : Type} → Program OneSig A → Counter A
  | _, .pure value => pure value
  | _, .vis operation next =>
      handler.handle operation >>= fun answer => interpret tick (next answer)

/-- **Falsifier for the morphism half.** `drifts h` agrees with every `h` on
every single operation, and still disagrees with `interpret nop` on two. -/
theorem agreement_alone_does_not_pin :
    (∀ (handler : Handler OneSig Counter) (operation : OneSig.Op),
      drifts handler (Program.perform operation) = handler.handle operation) ∧
    drifts nop twoOps ≠ interpret nop twoOps := by
  refine ⟨fun handler operation => ?_, ?_⟩
  · show handler.handle operation >>= (fun answer => interpret tick (.pure answer)) = _
    exact bind_pure (handler.handle operation)
  · intro h
    have h0 : (((), 1) : Unit × Nat) = ((), 0) := congrFun h 0
    exact absurd (congrArg Prod.snd h0) (by decide)

/-- The conjunction is what the library's pin consumes. `ignores` satisfies
`morphism` and fails `operations`; `drifts` satisfies `operations` and fails
`morphism`; neither is admitted. -/
example
    (candidate : Handler OneSig Counter → {A : Type} → Program OneSig A → Counter A)
    (morphism : ∀ handler,
      IsMonadMorphism OneSig (fun {_A} program => candidate handler program))
    (operations : ∀ (handler : Handler OneSig Counter) (operation : OneSig.Op),
      candidate handler (Program.perform operation) = handler.handle operation)
    (program : Program OneSig A) :
    candidate tick program = interpret tick program :=
  interpret_pinned candidate morphism operations tick program

end EffectsTest.Counterexamples.Algebra.InterpreterPin
