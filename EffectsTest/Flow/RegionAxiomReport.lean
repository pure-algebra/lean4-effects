import Effects

/-!
Kernel dependency report for the region packet
(`test/contracts/flow-regions.contract.md`, with the v0.8.0 clause structure
of `test/contracts/effects-boundary.contract.md`). Imports only the library
root. Every entry must stay within `propext` and `Quot.sound`.

`admitRegions_ok_erase` was the region layer's only exported theorem and had
no receipt at all until v0.8.0.
-/

#print axioms Effects.admitRegions_ok_erase

/-! The v0.8.0 clause structure and the law that the checker decides it. -/

#print axioms Effects.regionWF_iff_check
#print axioms Effects.RegionFlow.targetsLabelled_iff
#print axioms Effects.RegionFlow.targetsLabelled_nil
#print axioms Effects.RegionFlow.checkTable_eq_none_iff
#print axioms Effects.RegionFlow.checkTerm_eq_none_iff
#print axioms Effects.RegionFlow.checkBlock_eq_none_iff
