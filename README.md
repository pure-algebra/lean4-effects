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

Current state: **slice S2 of the split.** The nine algebra modules are here
under `Effects/Algebra/` with their lean4-effect4 history, renamed into the
`Effects` namespace and nothing else; `generated/algebra-parity.tsv` is the
byte-identical receipt against the source commit. The three batteries moved
with them and are declared red until slice S3 repoints them. The plan, its
rulings, and its exit gates are `docs/EFFECTS-SPLIT-PLAN.md` in
lean4-effect4.

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
