import Effects.Algebra.Handler.Category

/-!
# Signature morphisms

Rename the operations of a program along a morphism and pull handlers back
across it. The sum isomorphisms and the empty signature make `⊕ₛ` a
commutative idempotent monoid up to morphism, which is the normal form a
requirement row is. One law, `interpret_map`, connects renaming to pullback.
-/

namespace Effects

universe uOp uAns uS uT uU uN uP uTarget


/-- A signature morphism: rename every operation and pull the answer back. -/
structure Signature.Hom (S : Signature.{uS, uAns}) (T : Signature.{uT, uAns}) where
  op : S.Op → T.Op
  back : ∀ operation, T.Answer (op operation) → S.Answer operation

namespace Signature.Hom

def id (S : Signature.{uS, uAns}) : Hom S S := ⟨fun o => o, fun _ a => a⟩

def comp {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}}
    (f : Hom S T) (g : Hom T U) : Hom S U :=
  ⟨fun o => g.op (f.op o), fun o a => f.back o (g.back (f.op o) a)⟩

end Signature.Hom

/-- Rename the operations of a program along a morphism. -/
def Program.map {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {A : Type uAns}
    (f : Signature.Hom S T) : Program S A → Program T A
  | .pure value => .pure value
  | .vis operation next =>
      .vis (f.op operation) (fun answer => (next (f.back operation answer)).map f)

/-- Pull a handler for `T` back to a handler for `S`. -/
def Handler.pull {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {M : Type uAns → Type uTarget} [Monad M]
    (f : Signature.Hom S T) (handler : Handler T M) : Handler S M where
  handle operation := handler.handle (f.op operation) >>= fun answer => pure (f.back operation answer)

/-- The one law: interpreting a renamed program is interpreting through the
pulled-back handler. One induction, the same shape as `interpret_through`. -/
theorem interpret_map {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (f : Signature.Hom S T) (handler : Handler T M) {A : Type uAns}
    (program : Program S A) :
    interpret handler (program.map f) = interpret (handler.pull f) program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      show handler.handle (f.op operation) >>= _ =
        (handler.handle (f.op operation) >>= fun answer => pure (f.back operation answer)) >>= _
      rw [bind_assoc]
      simp only [pure_bind]
      exact bind_congr fun answer => ih (f.back operation answer)

theorem Program.map_id {S : Signature.{uS, uAns}} {A : Type uAns} (program : Program S A) :
    program.map (Signature.Hom.id S) = program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      exact congrArg (Program.vis operation) (funext fun answer => ih answer)

theorem Program.map_comp {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {U : Signature.{uU, uAns}} {A : Type uAns}
    (f : Signature.Hom S T) (g : Signature.Hom T U) (program : Program S A) :
    (program.map f).map g = program.map (f.comp g) := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      exact congrArg (Program.vis (g.op (f.op operation)))
        (funext fun answer => ih _)

/-! ### The sum isomorphisms and the empty signature -/

def Signature.empty : Signature.{uOp, uAns} := ⟨PEmpty, fun o => PEmpty.elim o⟩

namespace Signature.Hom

variable {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}}

def inl : Hom S (S ⊕ₛ T) := ⟨Sum.inl, fun _ a => a⟩
def inr : Hom T (S ⊕ₛ T) := ⟨Sum.inr, fun _ a => a⟩

def comm : Hom (S ⊕ₛ T) (T ⊕ₛ S) :=
  ⟨fun o => match o with | .inl s => .inr s | .inr t => .inl t,
   fun o => match o with | .inl _ => fun a => a | .inr _ => fun a => a⟩

def assoc : Hom (S ⊕ₛ (T ⊕ₛ U)) ((S ⊕ₛ T) ⊕ₛ U) :=
  ⟨fun o => match o with
     | .inl s => .inl (.inl s) | .inr (.inl t) => .inl (.inr t) | .inr (.inr u) => .inr u,
   fun o => match o with
     | .inl _ => fun a => a | .inr (.inl _) => fun a => a | .inr (.inr _) => fun a => a⟩

def assocInv : Hom ((S ⊕ₛ T) ⊕ₛ U) (S ⊕ₛ (T ⊕ₛ U)) :=
  ⟨fun o => match o with
     | .inl (.inl s) => .inl s | .inl (.inr t) => .inr (.inl t) | .inr u => .inr (.inr u),
   fun o => match o with
     | .inl (.inl _) => fun a => a | .inl (.inr _) => fun a => a | .inr _ => fun a => a⟩

/-- Idempotence: a duplicated summand collapses. This is why `R | R` is `R`. -/
def codiag : Hom (S ⊕ₛ S) S :=
  ⟨fun o => match o with | .inl s => s | .inr s => s,
   fun o => match o with | .inl _ => fun a => a | .inr _ => fun a => a⟩

def emptyLeft : Hom (Signature.empty.{uOp, uAns} ⊕ₛ S) S :=
  ⟨fun o => match o with | .inl e => PEmpty.elim e | .inr s => s,
   fun o => match o with | .inl e => PEmpty.elim e | .inr _ => fun a => a⟩

def emptyLeftInv : Hom S (Signature.empty.{uOp, uAns} ⊕ₛ S) := ⟨Sum.inr, fun _ a => a⟩

end Signature.Hom

/-- Reassociating a tower of handlers costs one `pull`, and the semantic law is
`interpret_map`; consumers never rebuild handlers by hand. -/
example {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}}
    {M : Type uAns → Type uTarget} [Monad M]
    (hs : Handler S M) (ht : Handler T M) (hu : Handler U M) :
    Handler (S ⊕ₛ (T ⊕ₛ U)) M :=
  ((hs.sum ht).sum hu).pull Signature.Hom.assoc

end Effects
