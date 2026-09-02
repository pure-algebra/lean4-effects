import Effects.Algebra.Handler.Category

/-!
# `E4-ALG-CE-004`: handler towers are a category, not one monoid

Local re-derivation, in slice S3 of the split, of the typing fact behind the
Foldlab witness (`library/cas/Cas/Backend/Universal.lean:739–790` at commit
`feb29321fd50204aa338209d313e84a3f8b71c66`, Apache-2.0): `through` changes
source and target signatures, so it is a binary operation on one carrier
only for endomorphisms `Handler S (Program S)`.

The witness is a rejected elaboration: composing a handler with itself when
its source and target signatures differ has no type. The positive half is
the library's own `Handler.through_endomorphism_monoid`.
-/

namespace EffectsTest.Counterexamples.Algebra.TowerCategory

open Effects

def Two : Signature.{0, 0} := ⟨Bool, fun _ => Unit⟩
def Three : Signature.{0, 0} := ⟨Fin 3, fun _ => Unit⟩
def One : Signature.{0, 0} := ⟨Unit, fun _ => Unit⟩

def twoToThree : Handler Two (Program Three) :=
  ⟨fun _ => Program.perform (0 : Fin 3)⟩

def threeToOne : Handler Three (Program One) :=
  ⟨fun _ => Program.perform ()⟩

/-- Across signatures the composite is typed, and its type moves. -/
def composite : Handler Two (Program One) := twoToThree.through threeToOne

/-- Associativity holds in that generality: the category law. -/
example (last : Handler One (Program One)) :
    (twoToThree.through threeToOne).through last =
      twoToThree.through (threeToOne.through last) :=
  Handler.through_assoc leftUnit_of_lawful bindAssoc_of_lawful
    twoToThree threeToOne last

/- **Falsifier.** The alleged global monoid would let `through` be applied to
`twoToThree` twice. It cannot: the second argument must handle `Three`. -/
/--
error: Application type mismatch
-/
#guard_msgs(error, substring := true) in
#check twoToThree.through twoToThree

/-- The monoid exists exactly on endomorphisms. -/
example (first second third : Handler One (Program One)) :
    (first.through second).through third =
        first.through (second.through third) ∧
      first.through identityHandler = first ∧
      identityHandler.through first = first :=
  Handler.through_endomorphism_monoid first second third

end EffectsTest.Counterexamples.Algebra.TowerCategory
