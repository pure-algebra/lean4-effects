import Effects.Algebra.Handler.Category

/-!
# Monad-homomorphism transport of handlers

`Handler.mapHom` moves a handler along a monad homomorphism; `interpret_mapHom`
is the one law. `Handler.through` is the special case `mapHom (interpretHom lower)`,
definitionally. `MonadHom.stateT` lifts a homomorphism through `StateT`, which
is state transport through a tower.
-/

namespace Effects

universe uOp uAns uS uT uU uN uP uTarget


structure MonadHom (M : Type uAns → Type uT) (N : Type uAns → Type uU) [Monad M] [Monad N] where
  app : ∀ {A : Type uAns}, M A → N A
  app_pure : ∀ {A : Type uAns} (a : A), app (pure a : M A) = (pure a : N A)
  app_bind : ∀ {A B : Type uAns} (m : M A) (k : A → M B),
    app (m >>= k) = app m >>= fun a => app (k a)

def Handler.mapHom {S : Signature.{uS, uAns}} {M : Type uAns → Type uT} {N : Type uAns → Type uU}
    [Monad M] [Monad N] (φ : MonadHom M N) (handler : Handler S M) : Handler S N :=
  ⟨fun operation => φ.app (handler.handle operation)⟩

theorem interpret_mapHom {S : Signature.{uS, uAns}} {M : Type uAns → Type uT}
    {N : Type uAns → Type uU} [Monad M] [Monad N]
    (φ : MonadHom M N) (handler : Handler S M) {A : Type uAns} (program : Program S A) :
    φ.app (interpret handler program) = interpret (handler.mapHom φ) program := by
  induction program with
  | pure value => exact φ.app_pure value
  | vis operation next ih =>
      show φ.app (handler.handle operation >>= _) = φ.app (handler.handle operation) >>= _
      rw [φ.app_bind]
      exact bind_congr fun answer => ih answer

/-- Interpretation itself is a monad homomorphism `Program T → M`. -/
def interpretHom {T : Signature.{uT, uAns}} {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (lower : Handler T M) : MonadHom (Program T) M where
  app := interpret lower
  app_pure _ := rfl
  app_bind m k := interpret_bind lower m k

/-- `through` is a special case of `mapHom`, definitionally. -/
theorem through_eq_mapHom {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (upper : Handler S (Program T)) (lower : Handler T M) :
    upper.through lower = upper.mapHom (interpretHom lower) := rfl

/-- Lifting a homomorphism through `StateT`: what `Layer.provide` with a `Ref` needs. -/
def MonadHom.stateT {M : Type uAns → Type uT} {N : Type uAns → Type uU} [Monad M] [Monad N]
    [LawfulMonad M] [LawfulMonad N] (φ : MonadHom M N) (σ : Type uAns) :
    MonadHom (StateT σ M) (StateT σ N) where
  app m := fun s => φ.app (m.run s)
  app_pure a := by funext s; exact φ.app_pure (a, s)
  app_bind m k := by
    funext s
    show φ.app (m.run s >>= fun p => (k p.1).run p.2) = _
    rw [φ.app_bind]
    rfl

end Effects
