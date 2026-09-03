# Flow attacks, v2 and v3

Packets: `test/contracts/flow-v2.contract.md` (rows `EF-FLOW-CE-001..003`)
and `test/contracts/flow-v3.contract.md` (rows `EF-FLOW-CE-007..008`).
Witnesses live in `EffectsTest/Counterexamples/Flow/FlowV2.lean` and
`EffectsTest/Counterexamples/Flow/FlowV3.lean`; rows in
`test/counterexamples/REGISTER.md`. The v2 section below is the breaker's
text, unchanged: the v2 witness module was red until the builder landed Flow
v2 (every `def`, `#guard`, and `example` in it), and is green now.

## Flow v2 attacks

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

## Flow v3 attacks

Both witnesses are green as authored; the module they live in
(`EffectsTest/Counterexamples/Flow/FlowV3.lean`) is reachable from
`EffectsTest.lean`, so the default build runs them.

## EF-FLOW-CE-007 — a caught failure unwinds regions

BROKE: the reading, natural for anyone porting `try`/`finally`, in which an
operation that fails inside a region closes that region, so the failure
successor of a `performCatch` is reached with the region already unwound and
may therefore be labelled with the enclosing scope, or with none at all.
WITNESS: `caughtInside`, a `RegionFlow` whose region 1 wraps a fallible `run`
with both successors of the catch labelled `some (regionId 1)`, is admitted
by `admitRegions`. `caughtOutside` is the same document with the failure
successor (block 3) moved outside region 1; `regionRefusal` returns
`some ⟨.successorLabel, some ⟨1⟩, some ⟨1⟩⟩`. CLASS: specification design.
FIXED-BY: nothing new — the failure edge is a declared successor like any
other, so the v0.5.0 clause `successorLabel` already condemns it. What Flow
v3 fixes is the *carrier*: `RawTerm.successors` lists `onError`, so the
region layer sees the failure edge at all. A caught failure continues inside
the still-open region, and unwinding is the uncaught case, which has no
successor to label.

## EF-FLOW-CE-008 — a branch on a value escapes the tape bound

BROKE: the claim that a finite decision tape bounds every run of an admitted
flow, under the reading in which a `branch` is a test of a computed value and
therefore not a decision at all. Nothing in the carrier can see the values a
loop computes, so a loop closed by such a `branch` would have no finite bound
of any kind — the same hole `EF-FLOW-CE-002` opened with `jump`, reopened by
a terminator that looks like control flow rather than nondeterminism.
WITNESS: `branchLoop` (block 1 branches back to block 0 on a `bool` answer)
is admitted and `cyclesChoose branchLoop = true`; the same graph with the
branch replaced by `jump` (`jumpLoop`) is refused with
`⟨.unchosenCycle, .block 0, .block ⟨0⟩⟩` and `cyclesChoose jumpLoop = false`.
The three projection receipts pin the reading that makes the difference:
`isChoose (branch …) = true`, `decision? (branch _ s _ _ _) = some s`, and
`successors (branch _ _ t f _) = [t, f]`. `branchOnNat`, which tests the
`nat` parameter, is refused with
`⟨.branchTestType, .term ⟨1⟩, .typeMismatch .bool .nat⟩`. CLASS: claim scope.
FIXED-BY: `branch` is a value test and a decision *site* at once, so
`CyclesWF` counts it and the tape bound of v2 survives verbatim; the test
operand carries `FlowAlphabet.boolTy`, enforced by the one clause v3 adds.
