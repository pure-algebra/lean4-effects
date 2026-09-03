import Effects.ListAux
import Effects.Algebra.Signature
import Effects.Algebra.Program
import Effects.Algebra.Handler
import Effects.Algebra.MonadLaws
import Effects.Algebra.Laws
import Effects.Algebra.Sum
import Effects.Algebra.Universal
import Effects.Algebra.Handler.Composition
import Effects.Algebra.Handler.Category
import Effects.Family
import Effects.Flow.Block
import Effects.Flow.Alphabet
import Effects.Flow.Raw
import Effects.Flow.Admission
import Effects.Flow.Checked
import Effects.Flow.Region
import Effects.Trace

/-!
# Effects

Standalone Lean library for a generic effect algebra: indexed signatures,
well-founded free programs, handlers, signature sums, model morphisms,
interpretation, and the universal laws (`Effects/Algebra`, frozen at v0.1.0);
named-operation families with the first-order alphabet embedding (v0.2.0,
with signature morphisms and monad-homomorphism transport moved to the opt-in
`Effects.Experimental` root at v0.8.0); and the generic
first-order flow with its checked admission (`Effects/Flow`, moved from
lean4-effect4 at v0.2.0). It has no Lake dependencies and no knowledge of any
host runtime. `docs/CLAIM-BOUNDARY.md` states what the theorems claim and what
they do not.
-/
