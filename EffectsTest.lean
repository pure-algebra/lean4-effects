import EffectsTest.Algebra.ExtractionContract
import EffectsTest.Algebra.RetainedClosureContract
import EffectsTest.Algebra.AxiomReport
import EffectsTest.Counterexamples.Algebra.InterpreterPin
import EffectsTest.Counterexamples.Algebra.FixedFuel
import EffectsTest.Counterexamples.Algebra.TowerCategory
import EffectsTest.Audit.AxiomGate

/-!
# Effects test battery

The default Lake build imports every admitted contract, attack, and kernel
dependency report through this root. A test file not reachable here is not a
passing gate.
-/

#effects_axiom_gate
