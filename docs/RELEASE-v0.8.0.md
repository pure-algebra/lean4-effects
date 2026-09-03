# Effects v0.8.0 — the consumer boundary

Released from `main`, tagged `v0.8.0`. Previous tag `v0.7.0` (`a117157`).

A release about what the package *shows*, not about a new semantic layer. It
answers findings #36 through #49 of lean4-effect4's
`docs/research/2026-09-03-survey-lean-core.md`. `docs/CLAIM-BOUNDARY.md`
§v0.8.0 owns what is and is not claimed; this file is the migration, written so
that the consumer's pin bump can be mechanical.

Packet: `test/contracts/effects-boundary.contract.md`. Battery:
`EffectsTest/Flow/BoundaryContract.lean`. Attacks: `EF-FLOW-CE-009`,
`EF-FLOW-CE-010`.

## The one breaking change: `errorTy` is an `Option`

```lean
-- v0.7.0
errorTy : Op → Ty
-- v0.8.0
errorTy : Op → Option Ty
```

**Every `FlowAlphabet` literal changes.** In lean4-effect4 there are two:

| File | Change |
| --- | --- |
| `Effect4/Target/TypeScript/ScriptFlow.lean:72` | `errorTy op := (OpSpec.at table op).errorTy` → `errorTy op := some (OpSpec.at table op).errorTy` |
| `Effect4Test/Semantics/FrameSimulationContract.lean:336` | `errorTy := fun _ => Ty.err` → `errorTy := fun _ => some Ty.err` |

Wrapping in `some` is the faithful translation of the v0.7.0 reading: an
alphabet that declared a total `errorTy` was claiming every operation can fail.
An alphabet that wants the new guarantee — that a catch is refused on an
operation that cannot fail — returns `none` for those operations instead. For
`ScriptFlow`'s `OpSpec`, the row spelling `"never"` is exactly that case, so
the honest port is

```lean
errorTy op := let spec := OpSpec.at table op
              if spec.errorTy == "never" then none else some spec.errorTy
```

which is a behaviour change and therefore a decision for the consumer's own
packet, not a mechanical one. `some (…)` keeps today's behaviour exactly.

### The clause that goes with it

`AdmissionClause.catchUnfailable` is new, at scan position 14, between
`branchTestType` and `unknownVariable`.

* `scan.length` is **19**, not 18. Any downstream `#guard` or `rfl` on the
  clause list or its length must be re-pinned.
* `TermsWF` is a six-fold conjunction; the sixth is
  `∀ block ∈ raw.blocks, CatchableWF alphabet block`. A downstream `Iff.rfl`
  receipt on `TermsWF` needs the sixth conjunct.
* `FlowWF` keeps its eight fields, and every retained theorem keeps its
  proposition, including `Diagnostic.clause_all_complete`.
* `ArgumentFailureValid.catchError` gains a `fails` hypothesis and binds the
  error type:

  ```lean
  -- v0.7.0
  (mismatch : alphabet.errorTy operationDef ≠ declared) :
    … (.typeMismatch (alphabet.errorTy operationDef) declared)
  -- v0.8.0
  (fails : alphabet.errorTy operationDef = some errorType)
  (mismatch : errorType ≠ declared) :
    … (.typeMismatch errorType declared)
  ```

* `SlotWF`'s `performCatch` error arm compares only when `errorTy` is `some`;
  `catchUnfailable`, which runs earlier, is what refuses the `none` case.

## `RegionWF` is a structure

`RegionWF alphabet flow` was `flow.check alphabet = none`. It is now a
fourteen-field structure, one field per `RegionClause` in clause order, with

```lean
theorem regionWF_iff_check (alphabet) (flow) :
    RegionWF alphabet flow ↔ flow.check alphabet = none
```

`CheckedRegionFlow`, `admitRegions`, `admitRegions_ok_erase` and the
`Decidable (RegionWF …)` instance are unchanged in type, so a consumer that
only *constructs* and *transports* region proofs needs no change.

A consumer that *reads* one does. `Effect4/Semantics/RegionSafety.lean` is the
whole of it in lean4-effect4: its seven private helpers exist to recover what
the fields now give directly.

| `RegionSafety.lean` helper | Replacement |
| --- | --- |
| `alternative_none` (line 29) | delete; nothing unfolds `check` any more |
| `table_checked` (33) | `RegionFlow.checkTable_eq_none_iff.mpr ⟨wf.duplicateRegion, wf.unknownParent, wf.continueOutside, wf.continueTyped⟩`, or use the four fields directly |
| `term_checked` (39) | `wf.retInside`, `wf.successorLabel`, `wf.enterParent`, `wf.enterBody`, `wf.acquireOutside`, `wf.acquireRelease`, `wf.leaveOutside`, `wf.leaveTyped` — whichever clause the caller wanted |
| `entry_outside` (53) | `wf.entryInside entry found` |
| `target_label` (62) | `RegionFlow.targetsLabelled_iff.mp good target mem block found`, or read `wf.successorLabel` at `RegionFlow.TargetsLabelled` directly |
| `continue_label` (68) | `(wf.continueOutside row mem)` gives `⟨target, found, labelled⟩` |
| the `checkTerm` unfoldings (85, 101, 123, 135) | the matching `RegionWF` field |

**`RegionFlow.checkBlock.checkTerm` no longer exists.** `checkTerm` was a
`where`-bound auxiliary and is now the named `RegionFlow.checkTerm alphabet
flow block`, so a `simp only [RegionFlow.checkBlock.checkTerm, …]` must be
re-spelled — but the point of this release is that it should be deleted
instead.

New region names, all public:

`RegionFlow.checkTerm`, `RegionFlow.TargetsLabelled`,
`RegionFlow.targetsLabelled_iff`, `RegionFlow.targetsLabelled_nil`,
`RegionTerm.labelledSuccessors`, the fourteen clause propositions
(`RegionFlow.DuplicateRegion`, `UnknownParent`, `ContinueOutside`,
`ContinueTyped`, `EntryOutside`, `UnknownLabel`, `RetOutside`,
`SuccessorLabel`, `EnterParent`, `EnterBody`, `AcquireInside`,
`AcquireRelease`, `LeaveInside`, `LeaveTyped`),
`RegionFlow.checkTable_eq_none_iff`, `checkTerm_eq_none_iff`,
`checkBlock_eq_none_iff`, `regionWF_iff_check`, and the fourteen
`RegionWF.*` projections.

## New public names — delete the downstream copies

Each of these existed in lean4-effect4 and should be deleted on the pin bump.

| Upstream name | Downstream copy to delete |
| --- | --- |
| `Effects.ListAux.length_filter_ne` | `Effect4/Semantics/Denotation.lean:393`, `Effect4/Semantics/Fuel.lean:37` |
| `Effects.ListAux.length_le_of_nodup_subset` | `Denotation.lean:416`, `Fuel.lean:57` |
| `Effects.reachableNoChoose_trans` | `Denotation.lean:434` |
| `Effects.RawFlow.reachSet_length_lt_of_edge` | `Denotation.lean:447` |
| `Effects.lookupBlock_id` | `Fuel.lean:73` (five call sites) |
| `Effects.mem_blockIds_of_lookup` | `Fuel.lean:80` |
| `Effects.FlowAlphabet.toAlphabet` | `Denotation.lean:36-48` — **delete the whole `namespace Effects` block**; nothing downstream may declare into this package's root namespace |

`Effects.ListAux.*` are generic in `α` with `DecidableEq`; the flow layer
instantiates them at `BlockId`, and `Fuel.lean`'s generic copies were already
in that shape.

Also new: `Effects.RawFlow.nodup_reachSet`,
`Effects.FlowAlphabet.toFamily`, `Effects.Diagnostic.diagnoseAll`,
`diagnoseAll_eq_nil_iff`, `diagnoseAll_valid`, `Effects.CatchableWF`,
`Effects.CatchFailureValid`.

## Privatised — nothing downstream used any of them

`RawFlow.insertAll`, `expand`, `saturate`, `allSuccessors`, `mem_insertAll`,
`length_le_insertAll`, `subset_of_length_insertAll_eq`, `nodup_insertAll`,
`insertAll_subset`, `expand_subset`, `mem_saturate_of_mem`, `saturate_sound`,
`saturate_closed_or_grows`, `nodup_saturate`, `saturate_subset`,
`mem_of_closed`, `noChooseSuccessors_subset`.

Still public: `RawFlow.reachSet`, `mem_reachSet`, `noChooseSuccessors`,
`mem_noChooseSuccessors`, and now `nodup_reachSet` and
`reachSet_length_lt_of_edge`. `reachSet` still closes under `decide`.

The one downstream use of a privatised name was `RawFlow.nodup_saturate` inside
`Denotation.lean:452`, which is in `reachSet_length_lt_of_edge` — the theorem
that moves upstream, so the use goes with it.

## Moved: `Effects.Morphism` and `Effects.Transport`

`import Effects` no longer provides `Signature.Hom`, `Program.map`,
`Handler.pull`, `interpret_map`, `Program.map_id`, `Program.map_comp`,
`Signature.empty`, the sum isomorphisms, `MonadHom`, `Handler.mapHom`,
`interpret_mapHom`, `interpretHom`, `through_eq_mapHom` or `MonadHom.stateT`.

They live behind `import Effects.Experimental` (or
`Effects.Experimental.Morphism` / `.Transport`). The declaration namespace is
unchanged — still `Effects` — so dot notation resolves as before and only the
import line moves. lean4-effect4 uses none of them, so nothing to do there.

`docs/CLAIM-BOUNDARY.md` §v0.8.0 states, once, what the label means: same axiom
ceiling and same trust gate, no frozen surface and no contract.

## Behaviour changes

`acquireRelease` now fires whenever `alphabet.lookup release = none`, whatever
the acquired operation is (`EF-FLOW-CE-009`). Erasure drops the release, so no
v2 clause can see it. **`admitRegions` admits exactly the flows it admitted
before**; the only difference is that some already-refused flows are now
refused by the region clause that names the real problem instead of by a v2
clause naming a different one. A downstream test asserting the *old* refusal
for a flow with both an unknown acquire and an unknown release must be
re-pinned.

## Build and gates

* `lakefile.toml` version `0.8.0`; `leanOptions = { autoImplicit = false,
  relaxedAutoImplicit = false }` on the `Effects` library. The nine
  `Effects/Algebra/` modules restore both options, with the parity receipt as
  the stated reason. This is invisible to a consumer: no name, type or
  universe-parameter order changed, verified against the v0.7.0 environment.
* The axiom gate refuses `sorry`, `axiom`, `native_decide`, `extern` and
  `implemented_by` as well as `unsafe` and `partial`, in both token shapes;
  refuses a bodyless `opaque`; and lets a generated auxiliary inherit its
  parent's admission only through a name Lean reserves.
* Four new fixtures under `test/fixtures/trust-gate/`;
  `./scripts/test-trust-gate.sh` plants nine defects and passes.
* Axiom receipts: 102 across six report modules, up from 91 across three.
  New: `EffectsTest/Flow/FlowV3AxiomReport.lean`,
  `EffectsTest/Flow/RegionAxiomReport.lean`,
  `EffectsTest/Family/AxiomReport.lean`,
  `EffectsTest/Experimental/AxiomReport.lean`. The union is still `propext`
  and `Quot.sound`.
* `./scripts/check-algebra-parity.sh` still passes: 215 constants identical to
  lean4-effect4 `217d3e4`.

## Consumer checklist

1. Bump the `effects` rev in `lake-manifest.json` (and pin the full 40-character
   hash, not an abbreviation).
2. Wrap `errorTy` in the two alphabet literals.
3. Re-pin `scan.length` to 19 and any `TermsWF` `Iff.rfl` receipt to six folds.
4. Rewrite `Effect4/Semantics/RegionSafety.lean` against the `RegionWF` fields;
   delete its seven private helpers.
5. Delete the `namespace Effects` block in `Effect4/Semantics/Denotation.lean`
   and the six duplicated lemmas in `Denotation.lean` and `Fuel.lean`.
6. Re-pin the `EF-FLOW-CE-016`-family region refusals if any of them names a
   flow with both an unknown acquire and an unknown release.
