import Effects.Experimental.Morphism
import Effects.Experimental.Transport

/-!
# Effects.Experimental — an opt-in root

`import Effects` does **not** bring this in. Everything reachable from here is
generic algebra that was stood up at v0.2.0 ahead of its contract packet, and
whose battery never followed: signature morphisms (`Effects/Experimental/Morphism.lean`)
and monad-homomorphism transport (`Effects/Experimental/Transport.lean`).

The ruling that put them here — what "experimental" commits this package to
and what it does not — is stated once, in `docs/CLAIM-BOUNDARY.md`, section
"v0.8.0". Nothing else restates it.

The declarations keep the `Effects` namespace, so `handler.mapHom` and
`program.map` still resolve by dot notation; only the module path and the
import changed. Kernel dependencies are receipted in
`EffectsTest/Experimental/AxiomReport.lean`, so the ceiling holds here as
everywhere else — what is missing is a contract and a battery, not a proof.
-/
