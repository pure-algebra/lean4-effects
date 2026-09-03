# Contract: regions over first-order flows (Effects v0.5.0)

Amended v0.8.0: the `performCatch` ruling below, `acquireRelease` on an
unknown release (`EF-FLOW-CE-009`), and `RegionWF` as a clause structure with
`regionWF_iff_check`.

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
releases innermost-first with that closing exit; an *uncaught* failure inside
a region closes it and every enclosing region with the failure; a `ret` is
only allowed outside every region. Attacks `EF-FLOW-CE-004..006`.

A `performCatch` (Flow v3, `flow-v3.contract.md`) is the exception to the
failure rule: its failure is *caught*, so it does not unwind. `EF-FLOW-CE-007`
is the attack that pinned the distinction, and `successorLabel` is what
enforces it — a `performCatch`'s failure edge is a declared successor like any
other and must carry the block's own region label.

### Ruling: catch-and-unwind is a non-goal (v0.8.0)

A catch whose handler runs *after* the enclosing region has closed and its
releases have run has no spelling in this layer, and is not a planned v0.9
terminator. `successorLabel` over both edges of a `performCatch` is a stated
rule, not an accident of the label check: a catch is lexically inside its
region. The unwind-then-handle shape is already a composition here — catch
inside the region, then `leave` — and the only piece it cannot spell, closing
a region *with* a failure so that enclosing regions unwind too, is
uncaught-failure semantics, which the runner owns and which no terminator in
this carrier names. Were a consumer to want it, it would be a `RegionRow`
change (a failure continuation beside `continue_`) in a new packet, not a
terminator.

## Acceptance

```text
lake env lean EffectsTest/Flow/RegionContract.lean
lake build
./scripts/test-trust-gate.sh
```
