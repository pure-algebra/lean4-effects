import Effects

/-!
Kernel dependency report for `Effects/Family.lean` and the flow alphabet's
bridge to it. Imports only the library root. Every entry must stay within
`propext` and `Quot.sound`.

The `Service`/`Handler` round trip is the claim that a service record *is* a
handler for its family's signature; it had no receipt before v0.8.0.
-/

#print axioms Effects.Family.Service.toHandler_ofHandler
#print axioms Effects.Family.Service.ofHandler_toHandler
#print axioms Effects.Alphabet.toFamily
#print axioms Effects.FlowAlphabet.toFamily
