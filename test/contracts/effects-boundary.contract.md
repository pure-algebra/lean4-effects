# Contract: the consumer boundary (Effects v0.8.0)

Light ceremony (operator ruling D2, as `flow-regions.contract.md`). This
packet owns the *boundary* changes of v0.8.0 — what a consumer sees — rather
than a new semantic layer. It amends, and does not supersede,
`flow-v3.contract.md` and `flow-regions.contract.md`.

Modules: `Effects/ListAux.lean`, `Effects/Flow/Alphabet.lean`,
`Effects/Flow/{Block,Raw,Admission,Region}.lean`.

Battery: `EffectsTest/Flow/BoundaryContract.lean`.

Axiom reports: `EffectsTest/Flow/FlowV3AxiomReport.lean`,
`EffectsTest/Flow/RegionAxiomReport.lean`,
`EffectsTest/Family/AxiomReport.lean`,
`EffectsTest/Experimental/AxiomReport.lean`.

Counterexamples: `EF-FLOW-CE-009` (an unknown release),
`EF-FLOW-CE-010` (a catch on an operation that cannot fail).

Origin: findings #36, #38, #39, #40, #43, #45 of
`docs/research/2026-09-03-survey-lean-core.md` in lean4-effect4.

## Why

Three shapes of the same defect. The package hid what its consumer needs and
exported what it does not (#39); the consumer therefore declared into
`namespace Effects` itself (#38) and reproved the hidden lemmas twice; the
region layer published its checker as its own specification, so the consumer
unfolded a `where`-bound auxiliary to recover a usable fact (#36); and the
one field admission never constrained, `errorTy`, made `performCatch`
admission weaker than it reads (#43).

## Frozen surface

| Name | Shape |
| --- | --- |
| `Effects.ListAux.length_filter_ne` | `a ∈ l → (l.filter (· ≠ a)).length + 1 ≤ l.length`, generic `α` with `DecidableEq` |
| `Effects.ListAux.length_le_of_nodup_subset` | `l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length`, generic `α` |
| `FlowAlphabet.toAlphabet` | `FlowAlphabet.{uTy, uOp} Ty → Alphabet.{uTy, uOp} Ty`, an `abbrev` |
| `FlowAlphabet.toFamily` | `toAlphabet` then `Alphabet.toFamily`, an `abbrev` |
| `lookupBlock_id` | `lookupBlock raw id = some block → block.id = id` |
| `mem_blockIds_of_lookup` | `lookupBlock raw id = some block → id ∈ raw.blocks.map RawBlock.id` |
| `reachableNoChoose_trans` | transitivity of `ReachableNoChoose` |
| `RawFlow.nodup_reachSet` | `(raw.reachSet start).Nodup` |
| `RawFlow.reachSet_length_lt_of_edge` | `CyclesWF raw → EdgeNoChoose raw s t → (raw.reachSet t).length < (raw.reachSet s).length` |
| `RegionWF` | a `structure` with one field per region clause |
| `regionWF_iff_check` | `RegionWF alphabet flow ↔ flow.check alphabet = none` |
| `FlowAlphabet.errorTy` | `Op → Option Ty` |
| `AdmissionClause.catchUnfailable` | the clause refusing a `performCatch` on an operation with no declared error type |
| `Diagnostic.diagnoseAll` | `scan.filterMap (diagnoseAt alphabet raw)`, with `diagnoseAll_eq_nil_iff` |

## Privatised

`RawFlow.insertAll`, `expand`, `saturate`, `allSuccessors` and their thirteen
lemmas (`mem_insertAll`, `length_le_insertAll`,
`subset_of_length_insertAll_eq`, `nodup_insertAll`, `insertAll_subset`,
`expand_subset`, `mem_saturate_of_mem`, `saturate_sound`,
`saturate_closed_or_grows`, `nodup_saturate`, `saturate_subset`,
`mem_of_closed`, `noChooseSuccessors_subset`) are `private`. They are
saturation scaffolding whose only purpose is `reachSet`; no consumer used one
of them. `reachSet`, `mem_reachSet`, `noChooseSuccessors` and
`mem_noChooseSuccessors` stay public, and `nodup_reachSet` and
`reachSet_length_lt_of_edge` are the public conclusions that replace them.

`RegionFlow.checkBlock.checkTerm` no longer exists: `checkBlock` calls a named
`checkTerm` instead of a `where`-bound auxiliary. The per-clause fields of
`RegionWF` are the supported replacement for unfolding it.

## Acceptance

```text
lake env lean EffectsTest/Flow/BoundaryContract.lean
lake build
./scripts/test-trust-gate.sh
```
