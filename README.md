# Effects

A standalone Lean 4 library for a generic effect algebra: indexed signatures,
well-founded free programs, handlers, signature sums, model morphisms,
interpretation, and the universal laws that connect them. It has no Lake
dependencies and no knowledge of any host runtime.

`Effects` is the umbrella for general effect implementations. Web-standard
reifications (WHATWG Streams first) build against it, and
[lean4-effect4](https://github.com/mepuka/lean4-effect4), the Effect
TypeScript reification, depends on it and later imports those standard
instances. Nothing depends in the other direction.

Current state: **v0.1.0, the algebra with its evidence.** The nine modules
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

Apache-2.0. See `LICENSE`.
