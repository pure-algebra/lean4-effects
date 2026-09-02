import Effects.Algebra.Signature
import Effects.Algebra.Program
import Effects.Algebra.Handler
import Effects.Algebra.MonadLaws
import Effects.Algebra.Laws
import Effects.Algebra.Sum
import Effects.Algebra.Universal
import Effects.Algebra.Handler.Composition
import Effects.Algebra.Handler.Category

/-!
# Effects

Standalone Lean library for a generic effect algebra: indexed signatures,
well-founded free programs, handlers, signature sums, model morphisms,
interpretation, and the universal laws. It has no Lake dependencies and no
knowledge of any host runtime. `docs/CLAIM-BOUNDARY.md` states what the
theorems claim and what they do not.
-/
