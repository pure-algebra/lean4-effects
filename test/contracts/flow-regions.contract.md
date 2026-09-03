# Contract: regions over first-order flows (Effects v0.5.0)

Light ceremony (operator ruling D2; the Flow v2 surface of
`flow-v2.contract.md` is not touched). Module: `Effects/Flow/Region.lean`.

## Frozen surface

| Name | Shape |
| --- | --- |
| `RegionId` | `value : Nat` |
| `RegionTerm` | `plain (term : RawTerm)`, `enter (region) (body) (args)`, `acquire (operation) (request) (release) (target) (args)`, `leave (value)` |
| `RegionRow Ty` | `id`, `parent : Option RegionId`, `continue_ : BlockId`, `resultTy : Ty` |
| `RegionBlock Ty` | `id`, `region : Option RegionId`, `params`, `term : RegionTerm` |
| `RegionFlow Ty` | the v2 header fields, `regions`, `blocks` |
| `RegionFlow.erase` | `enter r body args ↦ jump body args`; `acquire op req rel t args ↦ perform op req t args`; `leave v ↦ jump continue_ [v]` (an orphan jump outside every region) |
| `RegionClause`, `RegionDiagnostic`, `RegionFlow.check`, `RegionWF` | fourteen clauses, first failure, decidable |
| `CheckedRegionFlow alphabet` | `flow`, `regions : RegionWF`, `checked : CheckedFlow alphabet`, `erased : checked.erase = flow.erase` |
| `admitRegions`, `RegionRefusal` | region clauses first, then v2 on the erasure; `admitRegions_ok_erase` |

## Clauses (in order)

`duplicateRegion`, `unknownParent`, `continueOutside`, `continueTyped` (table);
`entryInside`; per block in declaration order: `unknownLabel`, then by term:
`retInside`, `successorLabel` (plain successors and `acquire` targets carry the
block's label), `enterParent`, `enterBody`, `acquireOutside`, `acquireRelease`
(the release takes the acquired answer), `leaveOutside`, `leaveTyped`.

## Semantics pinned here (the runner is lean4-effect4's)

A `leave` closes the innermost region with a value and runs its registered
releases innermost-first with that closing exit; a failure inside a region
closes it and every enclosing region with the failure; a `ret` is only
allowed outside every region. Attacks `EF-FLOW-CE-004..006`.

## Acceptance

```text
lake env lean EffectsTest/Flow/RegionContract.lean
lake build
./scripts/test-trust-gate.sh
```
