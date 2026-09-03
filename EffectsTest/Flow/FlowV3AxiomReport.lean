import Effects

/-!
Kernel dependency report for the Flow v3 packet
(`test/contracts/flow-v3.contract.md`) and the v0.8.0 boundary packet
(`test/contracts/effects-boundary.contract.md`). Imports only the library
root. Every entry must stay within `propext` and `Quot.sound`.

The sixteen v2 theorems are receipted in `FlowV2AxiomReport.lean` and are
re-proved, not restated, over the wider carrier; this file covers what v3 and
v0.8.0 add and what `FlowV2AxiomReport.lean` never named.
-/

/-! Flow v3: the four edge laws that make "every v2 shape reads as it did" a
theorem rather than a convention. -/

#print axioms Effects.RawTerm.argsAt_zero
#print axioms Effects.RawTerm.arityAt_zero
#print axioms Effects.RawTerm.argsAt_of_ne_one
#print axioms Effects.RawTerm.arityAt_of_ne_one

/-! v0.8.0: the published list auxiliaries. They are proved by induction here
precisely so that they stay inside the ceiling; these two lines are the
receipt for that claim. -/

#print axioms Effects.ListAux.length_filter_ne
#print axioms Effects.ListAux.length_le_of_nodup_subset

/-! v0.8.0: block resolution and the reachability measure. -/

#print axioms Effects.lookupBlock_id
#print axioms Effects.mem_blockIds_of_lookup
#print axioms Effects.reachableNoChoose_trans
#print axioms Effects.RawFlow.mem_reachSet
#print axioms Effects.RawFlow.nodup_reachSet
#print axioms Effects.RawFlow.reachSet_length_lt_of_edge
#print axioms Effects.RawFlow.mem_noChooseSuccessors

/-! v0.8.0: the all-clauses report. -/

#print axioms Effects.Diagnostic.diagnoseAll_eq_nil_iff
#print axioms Effects.Diagnostic.diagnoseAll_valid

/-! v0.8.0: the alphabet's embedding into the algebra's first-order carrier. -/

#print axioms Effects.FlowAlphabet.toAlphabet
