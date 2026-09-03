# Flow v2 attacks

Packet: `test/contracts/flow-v2.contract.md`. Witnesses live in
`EffectsTest/Counterexamples/Flow/FlowV2.lean`; rows in
`test/counterexamples/REGISTER.md`. The witness module is red until the
builder lands Flow v2 (every `def`, `#guard`, and `example` in it).

## EF-FLOW-CE-001 — one payload can carry the environment

BROKE: the v1 representation claim that one typed payload per block is
enough first-order content for a flow. WITNESS: design row.
`Effects/Flow/Block.lean` at `9595a88` (v0.3.1, SHA-256
`d5190349e7b85f0268a738b64de86361c22c48364dbaca9281485c4bc2d7f0ec`) has
`RawTerm.perform (operation : OperationId) (target : BlockId)` and
`RawBlock.inputTy : Ty`; `Effects/Flow/Raw.lean` (SHA-256
`e8608434403ad826e567405779d895188dc6fdf20d4c3553a206e16f929e4a66`) types a
`perform` by `targetBlock.inputTy = alphabet.answerTy operation`. The target
therefore receives exactly the answer, and `let x ← get; put x; return x`
has no block that holds `x` while `put` runs: after `get` the only payload
is `x`; after `put` the only payload is `()`. The v2 repair witness is
`incr` (admitted; `incrDropped` shows that the returned value is the one
carried across `put`). CLASS: representation. FIXED-BY: block parameter
lists; `perform`'s target receives `args ++ [answer]`; `ret` and the
`perform` request name a `Var`.

## EF-FLOW-CE-002 — a tape bounds every run without a cycle clause

BROKE: the claim that a finite decision tape bounds every run of an admitted
flow, so that admission needs no cycle clause (v1 `E4-FLOW-CE-005` chose to
admit closed cycles and "define divergence later"). WITNESS: a `jump`
self-loop admits under v0.3.1 `admit`; it has no decision site, so no tape
of any length bounds its run. Executed 2026-09-02 against `9595a88` with the
source below (also lean4-effect4 `c951711`
`Effect4Test/Flow/AdmissionContract.lean` lines 531–538, `selfCycleFlow`,
SHA-256 `dce29f4d9bc49ec778d345b23d2c3f758944425e0b7227b31d8c76843ecc810b`):

```lean
import Effects.Flow.Checked

namespace Probe
open Effects

inductive TyCode | unit | nat deriving DecidableEq, Repr
inductive ExampleOp | get | put deriving DecidableEq, Repr

def exampleLookup : OperationId → Option ExampleOp
  | ⟨0⟩ => some .get
  | ⟨1⟩ => some .put
  | _ => none

def alphabet : FlowAlphabet TyCode where
  id := ⟨7⟩
  Op := ExampleOp
  operationId
    | .get => ⟨0⟩
    | .put => ⟨1⟩
  lookup := exampleLookup
  requestTy
    | .get => .unit
    | .put => .nat
  answerTy
    | .get => .nat
    | .put => .unit
  lookup_operationId := by intro o; cases o <;> rfl
  operationId_of_lookup := by
    intro id o found
    cases o <;> rcases id with ⟨_ | _ | n⟩ <;> simp [exampleLookup] at found <;> rfl

def selfLoop : RawFlow TyCode :=
  ⟨⟨7⟩, [⟨0⟩], ⟨0⟩, .unit, .unit, [⟨⟨0⟩, .unit, .jump ⟨0⟩⟩]⟩

def isAdmitted (raw : RawFlow TyCode) : Bool :=
  match admit alphabet raw with
  | .ok _ => true
  | .error _ => false

#eval isAdmitted selfLoop
#guard isAdmitted selfLoop
end Probe
```

```text
$ lake env lean V1SelfLoop.lean
true
```

(`#eval` prints `true`; the `#guard` passes silently.) The v2 witnesses:
`unchosenLoop` is rejected with `⟨.unchosenCycle, .block 0, .block ⟨0⟩⟩` and
the sixteen earlier clauses return `none`; `chosenLoop` (a `choose` whose
left branch is itself) admits; `performLoop` shows a `perform` edge is not a
decision; `unreachableUnchosenLoop` shows the clause is whole-document,
reversing the cycle half of `E4-FLOW-CE-014`; `lateLoop` shows the condemned
block is the first declared block on the cycle. CLASS: claim scope.
FIXED-BY: `CyclesWF` (no `EdgeNoChoose` closes into a `ReachableNoChoose`
cycle), clause `unchosenCycle`, checker `cyclesChoose` with
`cyclesChoose_iff`.

## EF-FLOW-CE-003 — argument arity can be checked without types

BROKE: the claim, natural in an untyped block IR, that matching the argument
count against the receiver's parameter count is the edge check. WITNESS:
`rightArityWrongType` passes one `unit` argument to a block declaring one
`nat` parameter: `diagnoseAt … .argumentArity = none`, and `admit` fails
with `⟨.argumentTypeMismatch, .argument ⟨0⟩ 0 0, .typeMismatch .unit .nat⟩`.
The converse `wrongArity` fails `argumentArity` with `.arity 1 2` while
`argumentTypeMismatch` returns `none` on it. CLASS: specification design.
FIXED-BY: `argumentTypeMismatch` is a separate positional clause after
`argumentArity`, with a site naming the block, the receiver, and the
position.
