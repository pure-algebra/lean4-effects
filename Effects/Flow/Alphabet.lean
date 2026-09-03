import Effects.Family
import Effects.Flow.Block

/-!
# The flow alphabet's embedding into the algebra's first-order carrier

`FlowAlphabet` (`Effects/Flow/Block.lean`) is the admission boundary's closed
table: identity, executable lookup, and the type codes of every operation.
`Alphabet` (`Effects/Family.lean`) is the algebra's first-order table, the
same three type-code fields without the identities admission needs. This
module is the one bridge between them, and it is a separate module so that the
frozen flow fence (`Effects/Flow/{Block,Raw,Admission,Checked}.lean`) keeps
its `Std`-only import.

Added in v0.8.0 (survey finding #38): the declaration existed downstream, in
lean4-effect4's `Effect4/Semantics/Denotation.lean`, inside an
`open namespace Effects` block — a consumer declaring into its dependency's
root namespace, so that an upstream release adding this name would read as an
upstream bug. Its own comment already said where it belonged.
-/

namespace Effects

universe uTy uOp uAns

/-- The first-order alphabet under a flow alphabet: identity and the executable
lookup are admission's business, the operation table is the algebra's. -/
abbrev FlowAlphabet.toAlphabet {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty) :
    Alphabet.{uTy, uOp} Ty :=
  ⟨alphabet.Op, alphabet.requestTy, alphabet.answerTy⟩

/-- A flow alphabet embeds as a family once its type codes are denoted:
`toAlphabet` then `Alphabet.toFamily`, which is the embedding
`docs/CLAIM-BOUNDARY.md` promises downstream. -/
abbrev FlowAlphabet.toFamily {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty)
    (denote : Ty → Type uAns) : Family.{uOp, uAns, uAns} :=
  alphabet.toAlphabet.toFamily denote

end Effects
