import Effects.Algebra.Handler.Composition

/-!
# Category-shaped handler towers
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

theorem Handler.through_assoc [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (first : Handler S (Program T))
    (second : Handler T (Program U))
    (last : Handler U M) :
    (first.through second).through last =
      first.through (second.through last) :=
  Handler.ext fun operation =>
    interpret_through_of_equations leftUnit assoc second last
      (first.handle operation)

theorem Handler.through_identity_right
    (handler : Handler S (Program T)) :
    handler.through (identityHandler (S := T)) = handler :=
  Handler.ext fun operation => interpret_identity (handler.handle operation)

theorem Handler.through_identity_left [Monad M]
    (rightUnit : RightUnit M) (handler : Handler S M) :
    (identityHandler (S := S)).through handler = handler :=
  Handler.ext fun operation => rightUnit (handler.handle operation)

theorem Handler.through_endomorphism_monoid
    (first second third : Handler S (Program S)) :
    (first.through second).through third =
        first.through (second.through third) ∧
      first.through identityHandler = first ∧
      identityHandler.through first = first :=
  ⟨Handler.through_assoc leftUnit_of_lawful bindAssoc_of_lawful
      first second third,
    Handler.through_identity_right first,
    Handler.through_identity_left rightUnit_of_lawful first⟩

end Effects
