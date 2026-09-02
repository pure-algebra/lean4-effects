# Effects design basis

Status: adopted with slice S3 of the split, 2026-09-02. DB-01 below is
reproduced verbatim from lean4-effect4 `docs/DESIGN-BASIS.md` at commit
`217d3e4` (its section "DB-01 — `Program` is the well-founded higher-order
proof carrier"), with `Effect4` read as `Effects`; the universe policy that
follows is the one frozen by `test/contracts/algebra-extraction.contract.md`.
Effect4's DB-02 through DB-07 concern first-order flow, relational semantics,
logic, resources, and targets; they are Effect4-owned and are not copied.
`docs/CLAIM-BOUNDARY.md` states what the theorems built on this basis claim.

## DB-01 — `Program` is the well-founded higher-order proof carrier

The implemented algebra has the following shape:

```text
Signature.Op     : Type uOp
Signature.Answer : Signature.Op -> Type uAns

Program S A = pure A
            | vis (op : S.Op) (S.Answer op -> Program S A)

Handler S M = (op : S.Op) -> M (S.Answer op)
```

`Program` is higher-order as a representation because `vis` stores a Lean
continuation. It is an inductive, well-founded operation tree suited to monad
laws, interpreter laws, signature sums, handler composition, freeness, and
initiality arguments. It is not necessarily a finite node set or a uniformly
bounded-depth tree: an infinite answer type can index infinitely many distinct
continuation branches whose finite depths are unbounded. Every selected branch
is well-founded, which is the property structural recursion uses. `Program` is
not serializable syntax and receives no content hash, `DecidableEq`, or
generated TypeScript encoding.

This follows the free-model and induced-homomorphism organization in
[Plotkin and Pretnar](https://arxiv.org/abs/1312.1399) and the programming
interpretation demonstrated by
[Bauer and Pretnar's Eff](https://arxiv.org/abs/1203.1539). The literature
licenses the algebraic interface. It does not identify this particular Lean
inductive type with all effectful behavior.

`Handler.sum` is the operation for disjoint signatures. `Handler.through` is
the operation for collapsing an implementation through a second handler.
Categorical composition is stated across signatures; a monoid is available
only for endomorphisms. Implicit universe lifting is excluded. Any explicit
signature map or universe lift requires its own contract and coherence laws.

## Universe policy

Operation and answer universes are independent (`Signature.{uOp, uAns}`).
A program's result type lives in the answer universe, `Program S A` for
`A : Type uAns`, and a handler's target accepts exactly that universe,
`M : Type uAns → Type uTarget`. This is deliberate: it prevents constructing
a program that its handler kind cannot interpret, and it is attacked by
`E4-ALG-CE-005`, which is a guarded elaboration failure for a program whose
result universe is larger than the signature's answer universe. There is no
implicit universe lift anywhere in the library. Broader target-universe
comparison is an explicit-lift obligation for a later packet with its own
coherence laws, not a convenience instance.

## Equations on the target, not on the syntax

The sharp theorems require only the target-monad equations their proofs
consume: `LeftUnit`, `RightUnit`, and `BindAssoc` from `Effects.MonadLaws`.
The convenience forms accept `LawfulMonad`. No theorem strengthens
`Signature` with equations, and none quotients `Program` by them; a consumer
states its operation laws over an interpretation.
