import Effects.Experimental

/-!
Kernel dependency report for the opt-in `Effects.Experimental` root. Imports
only that root. Every entry must stay within `propext` and `Quot.sound`.

These five theorems have no contract and no battery — that is what
"experimental" means here, and `docs/CLAIM-BOUNDARY.md` §v0.8.0 states the
ruling. What they do have, from v0.8.0, is a receipt: their proofs are inside
the same ceiling as the rest of the tree, so a consumer who opts in is not
opting into a weaker trust boundary, only into an unfrozen surface.
-/

#print axioms Effects.interpret_map
#print axioms Effects.Program.map_id
#print axioms Effects.Program.map_comp
#print axioms Effects.interpret_mapHom
#print axioms Effects.through_eq_mapHom
