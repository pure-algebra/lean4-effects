import EffectsTest.Family.TowerSmoke
import EffectsTest.Family.AxiomReport
import EffectsTest.Experimental.AxiomReport
import EffectsTest.Algebra.ExtractionContract
import EffectsTest.Algebra.RetainedClosureContract
import EffectsTest.Algebra.AxiomReport
import EffectsTest.Counterexamples.Algebra.InterpreterPin
import EffectsTest.Counterexamples.Algebra.FixedFuel
import EffectsTest.Counterexamples.Algebra.TowerCategory
import EffectsTest.Trace.TraceContract
import EffectsTest.Trace.AxiomReport
import EffectsTest.Counterexamples.Trace.Around
import EffectsTest.Flow.FlowV2Contract
import EffectsTest.Flow.FlowV2AxiomReport
import EffectsTest.Flow.FlowV3Contract
import EffectsTest.Flow.FlowV3AxiomReport
import EffectsTest.Counterexamples.Flow.FlowV2
import EffectsTest.Counterexamples.Flow.FlowV3
import EffectsTest.Flow.RegionContract
import EffectsTest.Flow.RegionAxiomReport
import EffectsTest.Flow.BoundaryContract
import EffectsTest.Audit.AxiomGate

/-!
# Effects test battery

The default Lake build imports every admitted contract, attack, and kernel
dependency report through this root. A test file not reachable here is not a
passing gate.
-/

#effects_axiom_gate
