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

Current state: **slice S1 of the split, skeleton only.** The algebra modules
arrive in slice S2 by a history-preserving move from lean4-effect4. The plan,
its rulings, and its exit gates are `docs/EFFECTS-SPLIT-PLAN.md` in that
repository.

## Build and gates

```bash
lake build
```

The default build compiles the library, the test battery, and the axiom
gate: every declaration compiled from this tree must stay within `propext`
and `Quot.sound`, no authored `partial` or `unsafe` modifier is admitted, and
every `.lean` file must be reachable from the test root.

```bash
./scripts/test-trust-gate.sh
```

The self-test plants a `partial` declaration, an `unsafe` declaration, and an
unadmitted `Classical.choice` into a throwaway copy and checks that each is
rejected for the stated reason.

## License

Apache-2.0. See `LICENSE`.
