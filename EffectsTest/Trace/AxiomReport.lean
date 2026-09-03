import Effects.Trace
import EffectsTest.Counterexamples.Trace.Around

/-! Axiom receipts for the trace packet. Every entry must stay within
`propext` and `Quot.sound`. -/

#print axioms Effects.Trace.Outcome.map_id
#print axioms Effects.Trace.Outcome.map_comp
#print axioms Effects.Trace.project_project
#print axioms Effects.Trace.project_m2
#print axioms Effects.Trace.project_m1_m2
#print axioms Effects.Trace.agree_of_agree_m2
#print axioms Effects.Trace.Mask.m2_keeps
#print axioms Effects.interpret_projects_fst
#print axioms Effects.Family.Service.traced_projects
#print axioms Effects.Family.Service.interpret_traced_fst
#print axioms Effects.Family.Service.traced_perform
#print axioms Effects.interpret_projectsExcept_fst
#print axioms Effects.Family.Service.tracedExcept_projects
#print axioms Effects.Family.Service.interpret_tracedExcept_fst
#print axioms EffectsTest.Counterexamples.Trace.a_defect_rendered_as_a_failure
