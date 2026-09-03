import Effects.Algebra.Universal

/-!
# Handler composition
-/

/-
`autoImplicit` and `relaxedAutoImplicit` are off for the `Effects` library
(`lakefile.toml`) and are restored here, for these nine modules only.

`generated/algebra-parity.tsv` is a byte-identical receipt of every constant
these modules compile, compared against the lean4-effect4 commit they were
moved from — universe *parameter names* and full `pp.all` types included.
Binding `S`, `A` and their universes explicitly renames `u_1`/`u_2` and can
reorder a declaration's implicit binders, which breaks that receipt against a
commit that cannot be regenerated. The frozen v0.1.0 surface is worth more
here than the hygiene, and the parity gate is what enforces the trade:
`./scripts/check-algebra-parity.sh` fails the moment one of these files
changes shape. Every module outside `Effects/Algebra/` is bound explicitly.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Effects

/-- Collapse an implementation in `Program T` through a handler for `T`. -/
def Handler.through [Monad M]
    (upper : Handler S (Program T)) (lower : Handler T M) : Handler S M where
  handle operation := interpret lower (upper.handle operation)

theorem interpret_through [Monad M] [LawfulMonad M]
    (upper : Handler S (Program T)) (lower : Handler T M)
    (program : Program S A) :
    interpret lower (interpret upper program) =
      interpret (upper.through lower) program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      calc
        interpret lower (interpret upper (Program.vis operation next)) =
            interpret lower
              ((upper.handle operation).bind fun answer =>
                interpret upper (next answer)) := rfl
        _ = interpret lower (upper.handle operation) >>= fun answer =>
              interpret lower (interpret upper (next answer)) :=
            interpret_bind lower (upper.handle operation) _
        _ = interpret lower (upper.handle operation) >>= fun answer =>
              interpret (upper.through lower) (next answer) :=
            bind_congr fun answer => ih answer
        _ = interpret (upper.through lower) (Program.vis operation next) := rfl

theorem interpret_through_of_equations [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (upper : Handler S (Program T)) (lower : Handler T M)
    (program : Program S A) :
    interpret lower (interpret upper program) =
      interpret (upper.through lower) program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      calc
        interpret lower (interpret upper (Program.vis operation next)) =
            interpret lower
              ((upper.handle operation).bind fun answer =>
                interpret upper (next answer)) := rfl
        _ = interpret lower (upper.handle operation) >>= fun answer =>
              interpret lower (interpret upper (next answer)) :=
            interpret_bind_of_equations leftUnit assoc lower
              (upper.handle operation) _
        _ = interpret lower (upper.handle operation) >>= fun answer =>
              interpret (upper.through lower) (next answer) :=
            bind_congr fun answer => ih answer
        _ = interpret (upper.through lower) (Program.vis operation next) := rfl

end Effects
