# Effects

A standalone Lean 4 library for a generic effect algebra: indexed signatures,
well-founded free programs, handlers, signature sums, model morphisms,
interpretation, and the universal laws that connect them. It has no Lake
dependencies and no knowledge of any host runtime.

`Effects` is the umbrella for general effect implementations. Web-standard
reifications (WHATWG Streams first) build against it, and
[lean4-effect4](https://github.com/pure-algebra/lean4-effect4), the Effect
TypeScript reification, depends on it and later imports those standard
instances. Nothing depends in the other direction.

Current state: **v0.8.0.** The nine modules
under `Effects/Algebra/` carry their lean4-effect4 history; the only edits
since the move are the namespace lines, and `generated/algebra-parity.tsv` is
the byte-identical receipt of all 215 compiled constants against the source
commit. The two contract packets, the eight-row counterexample register with
local executable witnesses, the design basis, the claim boundary, and the
proof graph are in `test/` and `docs/`. The split plan, its rulings, and its
exit gates are `docs/EFFECTS-SPLIT-PLAN.md` in lean4-effect4.

Sixty named theorems have axiom receipts in
`EffectsTest/Algebra/AxiomReport.lean`; the union is `propext` and
`Quot.sound`.

Later bumps add, on top of the frozen algebra: model morphisms, transport,
and families (v0.2.0, morphisms and transport moved to the opt-in
`Effects.Experimental` root at v0.8.0); the service-level trace alphabet with
tracing services (v0.3.x); the first-order flow packet with block parameters
and the every-cycle-chooses clause (v0.4.0); regions over it (v0.5.0); the
trace alphabet re-frozen with `Outcome.defect`, a host defect distinct from a
failure, plus a `ToVal`-free `Outcome.map` with its identity and composition
laws (v0.6.0); Flow v3's `performCatch` and `branch` (v0.7.0); and the
boundary release of v0.8.0 — `errorTy : Op → Option Ty` with the
`catchUnfailable` clause, `RegionWF` as a clause structure, the published
reachability lemmas, and `diagnoseAll`. Each has its own entry in
`docs/CLAIM-BOUNDARY.md` and its own contract under `test/contracts/`;
`docs/RELEASE-v0.8.0.md` lists every downstream-visible change of the current
bump.

## Build and gates

```bash
lake build
```

The default build compiles the library, the test battery, and the axiom
gate: every declaration compiled from this tree must stay within `propext`
and `Quot.sound`, no authored `partial` or `unsafe` modifier is admitted, and
every `.lean` file must be reachable from the test root.

```bash
./scripts/check-algebra-parity.sh
```

Regenerates the parity receipt for the nine algebra modules and compares it
byte-for-byte with the committed receipt and with the receipt taken from
lean4-effect4 at the source commit.

```bash
./scripts/test-trust-gate.sh
```

The self-test plants a `partial` declaration, an `unsafe` declaration, and an
unadmitted `Classical.choice` into a throwaway copy and checks that each is
rejected for the stated reason.

## License

MIT, unified with the rest of the family. See `LICENSE`. Foldlab evidence
cited in `test/counterexamples/REGISTER.md` remains under Foldlab's own
Apache-2.0.
