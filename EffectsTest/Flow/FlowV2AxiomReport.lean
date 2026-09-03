import Effects

/-!
Kernel dependency report for the Flow v2 packet
(`test/contracts/flow-v2.contract.md`). Imports only the library root.
Every entry must stay within `propext` and `Quot.sound`.
-/

#print axioms Effects.FlowWF.reachable_declared
#print axioms Effects.cyclesChoose_iff
#print axioms Effects.Diagnostic.clause_all_complete
#print axioms Effects.diagnoseAt_some_valid
#print axioms Effects.FirstDiagnostic.condemns
#print axioms Effects.FirstDiagnostic.valid
#print axioms Effects.CheckedFlow.erase_eq_raw
#print axioms Effects.CheckedFlow.ext
#print axioms Effects.admit_sound
#print axioms Effects.admit_complete
#print axioms Effects.error_iff_not_wf
#print axioms Effects.error_iff_firstDiagnostic
#print axioms Effects.admit_error_valid
#print axioms Effects.erase_wf
#print axioms Effects.erase_admit
#print axioms Effects.admit_erase
