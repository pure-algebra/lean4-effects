import Effects.Flow.Checked

/-!
# Regions over first-order flows (v0.5.0)

A region is a scope: `enter` opens it, `acquire` performs an operation inside
it and registers a release for the answer, `leave` closes it with a value and
runs the registered releases innermost-first with the closing exit, after
which control continues at the region's `continue_` block with that value.
An *uncaught* failure inside a region closes it, and every enclosing region,
with the failure. A `performCatch` (Flow v3) is the exception: its failure is
*caught*, so it does not unwind. Nothing here says how a host does either:
the runner and its host agreement live in lean4-effect4
(`docs/TRACE-DAG.md`), and `EF-FLOW-CE-007` is the attack that pinned the
distinction.

Catch-and-unwind — a catch whose handler runs *after* the region has closed
and its releases have run — is a **non-goal**, not a deferred terminator.
`successorLabel` below requires every declared successor of a block to carry
the block's own region label, and a `performCatch`'s failure edge is a
declared successor like any other, so a catch is lexically inside its region
and a caught failure continues there. That is a stated rule, not a side
effect of the label check. The unwind-then-handle shape is already a
composition in this carrier — catch inside the region, then `leave` — and the
one piece it cannot spell, closing a region *with* a failure, is
uncaught-failure semantics, which the runner owns and which no terminator
here names. Should a consumer ever want it, it is a `RegionRow` change (a
failure continuation beside `continue_`), not a new terminator, and it is a
new packet.

The region layer erases to a Flow v2 graph (`RegionFlow.erase`): `enter` and
`leave` become jumps, `acquire` becomes a `perform`. The eighteen v3
admission clauses check the erased graph (identity, references, types,
cycles), and the region clauses below check what erasure forgets: region
ownership of every block, the shape of every `enter`, `acquire` and `leave`,
and that a `ret` never skips a region. The frozen flow surface is not
touched.
-/

namespace Effects

/-- Stable identity of a region. -/
structure RegionId where
  value : Nat
deriving DecidableEq, Repr

/-- A terminator of a region flow. -/
inductive RegionTerm where
  | plain (term : RawTerm)
  /-- Open `region`, continuing in `body` with `args`; the region's `continue_`
  block receives the value `leave` supplies. -/
  | enter (region : RegionId) (body : BlockId) (args : List Var)
  /-- Perform `operation` on `request`, register `release` for its answer in the
  innermost region, and continue in `target` with `args ++ [answer]`. -/
  | acquire (operation : OperationId) (request : Var) (release : OperationId)
      (target : BlockId) (args : List Var)
  /-- Close the innermost region with `value`. -/
  | leave (value : Var)
deriving DecidableEq, Repr

/-- The static row of a region: its parent, where control continues after it
closes, and the type of the value it closes with. -/
structure RegionRow (Ty : Type uTy) where
  id : RegionId
  parent : Option RegionId
  continue_ : BlockId
  resultTy : Ty
deriving DecidableEq, Repr

/-- A block with its region label (`none` outside every region). -/
structure RegionBlock (Ty : Type uTy) where
  id : BlockId
  region : Option RegionId
  params : List Ty
  term : RegionTerm
deriving DecidableEq, Repr

/-- A first-order flow with regions. -/
structure RegionFlow (Ty : Type uTy) where
  alphabet : AlphabetId
  roots : List BlockId
  entry : BlockId
  inputTy : Ty
  resultTy : Ty
  regions : List (RegionRow Ty)
  blocks : List (RegionBlock Ty)
deriving DecidableEq, Repr

namespace RegionFlow

def row? (flow : RegionFlow Ty) (id : RegionId) : Option (RegionRow Ty) :=
  flow.regions.find? fun row => row.id = id

def block? (flow : RegionFlow Ty) (id : BlockId) : Option (RegionBlock Ty) :=
  flow.blocks.find? fun block => block.id = id

/-- A block identity no declared block has; a `leave` outside every region
erases to a jump there, which v2 admission refuses as dangling. -/
def orphan (flow : RegionFlow Ty) : BlockId :=
  ⟨(flow.blocks.map fun block => block.id.value).foldl max 0 + 1⟩

/-- The v2 terminator a region terminator erases to. -/
def eraseTerm (flow : RegionFlow Ty) (block : RegionBlock Ty) : RawTerm :=
  match block.term with
  | .plain term => term
  | .enter _ body args => .jump body args
  | .acquire operation request _ target args => .perform operation request target args
  | .leave value =>
      match block.region.bind flow.row? with
      | some row => .jump row.continue_ [value]
      | none => .jump flow.orphan [value]

/-- The Flow v2 graph a region flow erases to. -/
def erase (flow : RegionFlow Ty) : RawFlow Ty :=
  { alphabet := flow.alphabet, roots := flow.roots, entry := flow.entry,
    inputTy := flow.inputTy, resultTy := flow.resultTy,
    blocks := flow.blocks.map fun block =>
      { id := block.id, params := block.params, term := flow.eraseTerm block } }

end RegionFlow

/-- The region clauses, checked after the region table and before v2 admission. -/
inductive RegionClause where
  /-- two region rows share an identity -/
  | duplicateRegion
  /-- a region's parent is not a declared region -/
  | unknownParent
  /-- a region's `continue_` block does not resolve or is not labelled with its parent -/
  | continueOutside
  /-- a region's `continue_` block does not declare exactly `[resultTy]` -/
  | continueTyped
  /-- a block's label is not a declared region -/
  | unknownLabel
  /-- the entry block is inside a region -/
  | entryInside
  /-- a plain successor or an `acquire` target carries another label -/
  | successorLabel
  /-- an `enter` opens a region whose parent is not the block's label -/
  | enterParent
  /-- an `enter`'s body is not labelled with the region it opens -/
  | enterBody
  /-- an `acquire` outside every region -/
  | acquireOutside
  /-- a release operation is unknown, or is known and does not take the
  acquired answer. The unknown case does not depend on the acquired operation:
  erasure drops the release, so no v2 clause ever sees it (`EF-FLOW-CE-009`). -/
  | acquireRelease
  /-- a `leave` outside every region -/
  | leaveOutside
  /-- a `leave` value is not the region's result type -/
  | leaveTyped
  /-- a `ret` inside a region would skip its releases -/
  | retInside
deriving DecidableEq, Repr

/-- A refused region flow: the clause, the block (when block-local) and the
region (when one is named). -/
structure RegionDiagnostic where
  clause : RegionClause
  block : Option BlockId
  region : Option RegionId
deriving DecidableEq, Repr

namespace RegionFlow

/-- The region table: unique identities, declared parents, and a typed,
correctly labelled `continue_` per region. -/
def checkTable [DecidableEq Ty] (flow : RegionFlow Ty) : Option RegionDiagnostic :=
  if !(flow.regions.map fun row => row.id).Nodup then some ⟨.duplicateRegion, none, none⟩
  else
    (flow.regions.findSome? fun row =>
      match row.parent with
      | some parent => if (flow.row? parent).isNone then some ⟨.unknownParent, none, some row.id⟩ else none
      | none => none) <|>
    (flow.regions.findSome? fun row =>
      match flow.block? row.continue_ with
      | none => some ⟨.continueOutside, some row.continue_, some row.id⟩
      | some target =>
          if target.region != row.parent then some ⟨.continueOutside, some target.id, some row.id⟩
          else if target.params != [row.resultTy] then some ⟨.continueTyped, some target.id, some row.id⟩
          else none)

/-- Whether every resolving target carries `label`; a missing target is the
v2 clause `danglingSuccessor`'s business. -/
def targetsLabelled (flow : RegionFlow Ty) (label : Option RegionId) (targets : List BlockId) : Bool :=
  targets.all fun target =>
    match flow.block? target with
    | some block => block.region == label
    | none => true

/-- Prop form of `targetsLabelled`: every resolving target carries `label`.
A missing target is the v2 clause `danglingSuccessor`'s business. -/
def TargetsLabelled (flow : RegionFlow Ty) (label : Option RegionId)
    (targets : List BlockId) : Prop :=
  ∀ target ∈ targets, ∀ block, flow.block? target = some block → block.region = label

@[simp] theorem targetsLabelled_nil (flow : RegionFlow Ty) (label : Option RegionId) :
    flow.targetsLabelled label [] = true := rfl

theorem targetsLabelled_iff [DecidableEq Ty] {flow : RegionFlow Ty}
    {label : Option RegionId} {targets : List BlockId} :
    flow.targetsLabelled label targets = true ↔ flow.TargetsLabelled label targets := by
  simp only [targetsLabelled, TargetsLabelled, List.all_eq_true]
  constructor
  · intro checked target mem block found
    have := checked target mem
    simpa [found] using this
  · intro holds target mem
    cases found : flow.block? target with
    | none => simp
    | some block => simpa [found] using holds target mem block found

/-- The successors of a region terminator that must carry the block's own
region label: the plain terminator's own successors and an `acquire`'s target.
An `enter` hands its body to the region it opens and a `leave` jumps to the
region's `continue_`, so neither is checked here. -/
def _root_.Effects.RegionTerm.labelledSuccessors : RegionTerm → List BlockId
  | .plain term => term.successors
  | .acquire _ _ _ target _ => [target]
  | .enter _ _ _ => []
  | .leave _ => []

/-- The region clauses of one block's terminator, checked after its label
resolves. A named definition rather than a `where`-bound auxiliary: a
downstream module had to unfold the auxiliary to recover a usable fact, which
is what `RegionWF`'s clause fields exist to make unnecessary. -/
def checkTerm [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (block : RegionBlock Ty) : Option RegionDiagnostic :=
    match block.term with
    | .plain (.ret _) =>
        if block.region.isSome then some ⟨.retInside, some block.id, block.region⟩ else none
    | .plain term =>
        if flow.targetsLabelled block.region term.successors then none
        else some ⟨.successorLabel, some block.id, block.region⟩
    | .enter region body _ =>
        match flow.row? region with
        | none => some ⟨.enterParent, some block.id, some region⟩
        | some row =>
            if row.parent != block.region then some ⟨.enterParent, some block.id, some region⟩
            else if !flow.targetsLabelled (some region) [body] then some ⟨.enterBody, some block.id, some region⟩
            else none
    | .acquire operation _ release target _ =>
        if block.region.isNone then some ⟨.acquireOutside, some block.id, none⟩
        else if !flow.targetsLabelled block.region [target] then some ⟨.successorLabel, some block.id, block.region⟩
        else
          -- The release is checked on its own first. `eraseTerm` drops it, so
          -- v2's `unknownOperation` never sees it; keying this arm on the
          -- *acquired* operation left an unknown release invisible whenever the
          -- acquired operation was unknown too, and it surfaced only on a
          -- second round (`EF-FLOW-CE-009`).
          match alphabet.lookup release with
          | none => some ⟨.acquireRelease, some block.id, block.region⟩
          | some releaser =>
              match alphabet.lookup operation with
              | none => none
              | some acquired =>
                  if alphabet.requestTy releaser = alphabet.answerTy acquired then none
                  else some ⟨.acquireRelease, some block.id, block.region⟩
    | .leave value =>
        match block.region.bind flow.row? with
        | none => some ⟨.leaveOutside, some block.id, block.region⟩
        | some row =>
            match block.params[value.index]? with
            | some ty => if ty = row.resultTy then none else some ⟨.leaveTyped, some block.id, some row.id⟩
            | none => none

/-- The region clauses of one block: its label resolves, then its terminator. -/
def checkBlock [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (block : RegionBlock Ty) : Option RegionDiagnostic :=
  match block.region with
  | some label =>
      if (flow.row? label).isNone then some ⟨.unknownLabel, some block.id, some label⟩
      else flow.checkTerm alphabet block
  | none => flow.checkTerm alphabet block

/-- The first failing region clause, if any. -/
def check [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) :
    Option RegionDiagnostic :=
  flow.checkTable <|>
  (match flow.block? flow.entry with
   | some entry => if entry.region.isSome then some ⟨.entryInside, some entry.id, entry.region⟩ else none
   | none => none) <|>
  flow.blocks.findSome? (flow.checkBlock alphabet)

end RegionFlow
namespace RegionFlow

/-! ## The region clauses as propositions

One `Prop` per clause of `RegionClause`, in the same shape the flow layer one
directory up uses for `OperandsWF` and `BranchTestWF`: a `match` on the thing
the clause is about, `True` where the clause does not apply. `RegionWF` below
is the structure of these, and `regionWF_iff_check` is the law that the
checker decides exactly them. -/

/-- `duplicateRegion`. -/
def DuplicateRegion (flow : RegionFlow Ty) : Prop :=
  (flow.regions.map fun row => row.id).Nodup

/-- `unknownParent`: a region's parent is a declared region. -/
def UnknownParent (flow : RegionFlow Ty) : Prop :=
  ∀ row ∈ flow.regions,
    match row.parent with
    | some parent => (flow.row? parent).isSome = true
    | none => True

/-- `continueOutside`: a region's `continue_` resolves and is labelled with
the region's own parent. -/
def ContinueOutside (flow : RegionFlow Ty) : Prop :=
  ∀ row ∈ flow.regions, ∃ target,
    flow.block? row.continue_ = some target ∧ target.region = row.parent

/-- `continueTyped`: a region's `continue_` declares exactly `[resultTy]`. -/
def ContinueTyped (flow : RegionFlow Ty) : Prop :=
  ∀ row ∈ flow.regions, ∀ target,
    flow.block? row.continue_ = some target → target.params = [row.resultTy]

/-- `entryInside`: the entry block is outside every region. -/
def EntryOutside (flow : RegionFlow Ty) : Prop :=
  ∀ entry, flow.block? flow.entry = some entry → entry.region = none

/-- `unknownLabel`: a block's label is a declared region. -/
def UnknownLabel (flow : RegionFlow Ty) (block : RegionBlock Ty) : Prop :=
  match block.region with
  | some label => (flow.row? label).isSome = true
  | none => True

/-- `retInside`: a `ret` is outside every region, so it skips no releases. -/
def RetOutside (block : RegionBlock Ty) : Prop :=
  match block.term with
  | .plain (.ret _) => block.region = none
  | _ => True

/-- `successorLabel`: every plain successor and every `acquire` target carries
the block's own label. -/
def SuccessorLabel (flow : RegionFlow Ty) (block : RegionBlock Ty) : Prop :=
  flow.TargetsLabelled block.region block.term.labelledSuccessors

/-- `enterParent`: an `enter` opens a declared region whose parent is the
block's own label. -/
def EnterParent (flow : RegionFlow Ty) (block : RegionBlock Ty) : Prop :=
  match block.term with
  | .enter region _ _ => ∃ row, flow.row? region = some row ∧ row.parent = block.region
  | _ => True

/-- `enterBody`: an `enter`'s body is labelled with the region it opens. -/
def EnterBody (flow : RegionFlow Ty) (block : RegionBlock Ty) : Prop :=
  match block.term with
  | .enter region body _ => flow.TargetsLabelled (some region) [body]
  | _ => True

/-- `acquireOutside`: an `acquire` is inside a region. -/
def AcquireInside (block : RegionBlock Ty) : Prop :=
  match block.term with
  | .acquire _ _ _ _ _ => block.region.isSome = true
  | _ => True

/-- `acquireRelease`: the release is a declared operation, and takes the
acquired answer when the acquired operation is declared too. Its declaredness
does not depend on the acquired operation (`EF-FLOW-CE-009`). -/
def AcquireRelease (alphabet : FlowAlphabet Ty) (block : RegionBlock Ty) : Prop :=
  match block.term with
  | .acquire operation _ release _ _ =>
      ∃ releaser, alphabet.lookup release = some releaser ∧
        ∀ acquired, alphabet.lookup operation = some acquired →
          alphabet.requestTy releaser = alphabet.answerTy acquired
  | _ => True

/-- `leaveOutside`: a `leave` closes a declared region. -/
def LeaveInside (flow : RegionFlow Ty) (block : RegionBlock Ty) : Prop :=
  match block.term with
  | .leave _ => (block.region.bind flow.row?).isSome = true
  | _ => True

/-- `leaveTyped`: a `leave` value carries the region's result type. -/
def LeaveTyped (flow : RegionFlow Ty) (block : RegionBlock Ty) : Prop :=
  match block.term with
  | .leave value =>
      ∀ row, block.region.bind flow.row? = some row →
        ∀ ty, block.params[value.index]? = some ty → ty = row.resultTy
  | _ => True

end RegionFlow

/--
Exactly the fourteen region clauses, one field each, in `RegionClause` order.

Until v0.8.0 this was `flow.check alphabet = none` — a statement about a
*program*, not about a flow — with no way to read a clause off it, so a
consumer that wanted one unfolded the checker and a `where`-bound auxiliary.
`regionWF_iff_check` is the soundness-and-completeness law that replaces that,
mirroring `flowWF_iff_clauses` one directory up, and every field below is a
projection a consumer applies directly.
-/
structure RegionWF [DecidableEq Ty] (alphabetDef : FlowAlphabet Ty)
    (flow : RegionFlow Ty) : Prop where
  duplicateRegion : flow.DuplicateRegion
  unknownParent : flow.UnknownParent
  continueOutside : flow.ContinueOutside
  continueTyped : flow.ContinueTyped
  entryInside : flow.EntryOutside
  unknownLabel : ∀ block ∈ flow.blocks, flow.UnknownLabel block
  retInside : ∀ block ∈ flow.blocks, RegionFlow.RetOutside block
  successorLabel : ∀ block ∈ flow.blocks, flow.SuccessorLabel block
  enterParent : ∀ block ∈ flow.blocks, flow.EnterParent block
  enterBody : ∀ block ∈ flow.blocks, flow.EnterBody block
  acquireOutside : ∀ block ∈ flow.blocks, RegionFlow.AcquireInside block
  acquireRelease : ∀ block ∈ flow.blocks, RegionFlow.AcquireRelease alphabetDef block
  leaveOutside : ∀ block ∈ flow.blocks, flow.LeaveInside block
  leaveTyped : ∀ block ∈ flow.blocks, flow.LeaveTyped block

private theorem alternative_none {α : Type u} {a b : Option α} :
    (a <|> b) = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp

namespace RegionFlow

theorem checkTable_eq_none_iff [DecidableEq Ty] {flow : RegionFlow Ty} :
    flow.checkTable = none ↔
      flow.DuplicateRegion ∧ flow.UnknownParent ∧
        flow.ContinueOutside ∧ flow.ContinueTyped := by
  unfold checkTable DuplicateRegion UnknownParent ContinueOutside ContinueTyped
  constructor
  · intro clear
    split at clear
    · simp at clear
    · rename_i notDuplicate
      obtain ⟨parents, continues⟩ := alternative_none.mp clear
      refine ⟨by simpa using notDuplicate, ?_, ?_, ?_⟩
      · intro row mem
        have h := List.findSome?_eq_none_iff.mp parents row mem
        cases parent : row.parent with
        | none => trivial
        | some parentId =>
            simp only [parent] at h
            cases resolved : flow.row? parentId with
            | none => simp [resolved] at h
            | some value => simp [resolved]
      · intro row mem
        have h := List.findSome?_eq_none_iff.mp continues row mem
        cases found : flow.block? row.continue_ with
        | none => simp [found] at h
        | some target =>
            simp only [found] at h
            refine ⟨target, rfl, ?_⟩
            by_cases labelled : target.region = row.parent
            · exact labelled
            · rw [if_pos (bne_iff_ne.mpr labelled)] at h; simp at h
      · intro row mem target found
        have h := List.findSome?_eq_none_iff.mp continues row mem
        simp only [found] at h
        by_cases labelled : target.region = row.parent
        · rw [if_neg (by simp [labelled])] at h
          by_cases typedEq : target.params = [row.resultTy]
          · exact typedEq
          · rw [if_pos (bne_iff_ne.mpr typedEq)] at h; simp at h
        · rw [if_pos (bne_iff_ne.mpr labelled)] at h; simp at h
  · rintro ⟨nodup, parents, continues, typed⟩
    rw [if_neg (by simp [nodup])]
    refine alternative_none.mpr ⟨?_, ?_⟩
    · apply List.findSome?_eq_none_iff.mpr
      intro row mem
      have h := parents row mem
      cases parent : row.parent with
      | none => rfl
      | some parentId =>
          simp only [parent] at h ⊢
          cases resolved : flow.row? parentId with
          | none => simp [resolved] at h
          | some value => simp
    · apply List.findSome?_eq_none_iff.mpr
      intro row mem
      obtain ⟨target, found, labelled⟩ := continues row mem
      simp only [found]
      rw [if_neg (by simp [labelled]),
        if_neg (by simp [typed row mem target found])]

theorem checkTerm_eq_none_iff [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} {block : RegionBlock Ty} :
    flow.checkTerm alphabet block = none ↔
      (RetOutside block ∧ flow.SuccessorLabel block ∧
        flow.EnterParent block ∧ flow.EnterBody block ∧
        AcquireInside block ∧ AcquireRelease alphabet block ∧
        flow.LeaveInside block ∧ flow.LeaveTyped block) := by
  unfold checkTerm RetOutside SuccessorLabel EnterParent EnterBody
    AcquireInside AcquireRelease LeaveInside LeaveTyped
    RegionTerm.labelledSuccessors
  cases term : block.term with
  | plain raw =>
      cases raw with
      | ret value =>
          cases region : block.region <;>
            simp [TargetsLabelled, RawTerm.successors]
      | jump target args =>
          cases labelled :
              flow.targetsLabelled block.region (RawTerm.jump target args).successors <;>
            simp [labelled, ← targetsLabelled_iff]
      | perform operation request target args =>
          cases labelled : flow.targetsLabelled block.region
              (RawTerm.perform operation request target args).successors <;>
            simp [labelled, ← targetsLabelled_iff]
      | choose decision left right args =>
          cases labelled : flow.targetsLabelled block.region
              (RawTerm.choose decision left right args).successors <;>
            simp [labelled, ← targetsLabelled_iff]
      | performCatch operation request target args onError errorArgs =>
          cases labelled : flow.targetsLabelled block.region
              (RawTerm.performCatch operation request target args onError
                errorArgs).successors <;>
            simp [labelled, ← targetsLabelled_iff]
      | branch test site onTrue onFalse args =>
          cases labelled : flow.targetsLabelled block.region
              (RawTerm.branch test site onTrue onFalse args).successors <;>
            simp [labelled, ← targetsLabelled_iff]
  | enter region body args =>
      cases found : flow.row? region with
      | none => simp [found, TargetsLabelled]
      | some row =>
          by_cases parent : row.parent = block.region <;>
            cases labelled : flow.targetsLabelled (some region) [body] <;>
              simp [found, parent, labelled, ← targetsLabelled_iff]
  | acquire operation request release target args =>
      cases region : block.region with
      | none => simp [TargetsLabelled]
      | some label =>
          cases labelled : flow.targetsLabelled (some label) [target]
          · simp [labelled, ← targetsLabelled_iff]
          · cases releaser : alphabet.lookup release with
            | none => simp [labelled, releaser, ← targetsLabelled_iff]
            | some releaserDef =>
                cases acquired : alphabet.lookup operation with
                | none =>
                    simp [labelled, releaser, acquired, ← targetsLabelled_iff]
                | some acquiredDef =>
                    by_cases typed :
                        alphabet.requestTy releaserDef = alphabet.answerTy acquiredDef <;>
                      simp [labelled, releaser, acquired, typed,
                        ← targetsLabelled_iff]
  | leave value =>
      cases found : block.region.bind flow.row? with
      | none => simp [TargetsLabelled]
      | some row =>
          cases typedAt : block.params[value.index]? with
          | none => simp [typedAt, TargetsLabelled]
          | some ty =>
              by_cases typed : ty = row.resultTy <;>
                simp [typedAt, typed, TargetsLabelled]

theorem checkBlock_eq_none_iff [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} {block : RegionBlock Ty} :
    flow.checkBlock alphabet block = none ↔
      (flow.UnknownLabel block ∧ flow.checkTerm alphabet block = none) := by
  unfold checkBlock UnknownLabel
  cases region : block.region with
  | none => simp
  | some label =>
      cases found : flow.row? label with
      | none => simp [found]
      | some row => simp [found]

end RegionFlow

/-- The region clause structure is exactly what the checker decides: sound and
complete, the region layer's counterpart of `flowWF_iff_clauses`. Every
consumer that needs a clause reads a field of `RegionWF`; nothing downstream
unfolds `check`. -/
theorem regionWF_iff_check [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) :
    RegionWF alphabet flow ↔ flow.check alphabet = none := by
  unfold RegionFlow.check
  rw [alternative_none, alternative_none]
  constructor
  · intro wf
    refine ⟨RegionFlow.checkTable_eq_none_iff.mpr
      ⟨wf.duplicateRegion, wf.unknownParent, wf.continueOutside, wf.continueTyped⟩,
      ?_, ?_⟩
    · cases found : flow.block? flow.entry with
      | none => rfl
      | some entry => simp [wf.entryInside entry found]
    · apply List.findSome?_eq_none_iff.mpr
      intro block mem
      exact RegionFlow.checkBlock_eq_none_iff.mpr
        ⟨wf.unknownLabel block mem, RegionFlow.checkTerm_eq_none_iff.mpr
          ⟨wf.retInside block mem, wf.successorLabel block mem,
           wf.enterParent block mem, wf.enterBody block mem,
           wf.acquireOutside block mem, wf.acquireRelease block mem,
           wf.leaveOutside block mem, wf.leaveTyped block mem⟩⟩
  · rintro ⟨table, entry, blocks⟩
    obtain ⟨nodup, parents, continues, typed⟩ :=
      RegionFlow.checkTable_eq_none_iff.mp table
    have termClear : ∀ block ∈ flow.blocks,
        flow.checkTerm alphabet block = none := fun block mem =>
      (RegionFlow.checkBlock_eq_none_iff.mp
        (List.findSome?_eq_none_iff.mp blocks block mem)).2
    exact {
      duplicateRegion := nodup
      unknownParent := parents
      continueOutside := continues
      continueTyped := typed
      entryInside := by
        intro entryBlock found
        simp only [found] at entry
        cases region : entryBlock.region with
        | none => rfl
        | some label => simp [region] at entry
      unknownLabel := fun block mem =>
        (RegionFlow.checkBlock_eq_none_iff.mp
          (List.findSome?_eq_none_iff.mp blocks block mem)).1
      retInside := fun block mem =>
        (RegionFlow.checkTerm_eq_none_iff.mp (termClear block mem)).1
      successorLabel := fun block mem =>
        (RegionFlow.checkTerm_eq_none_iff.mp (termClear block mem)).2.1
      enterParent := fun block mem =>
        (RegionFlow.checkTerm_eq_none_iff.mp (termClear block mem)).2.2.1
      enterBody := fun block mem =>
        (RegionFlow.checkTerm_eq_none_iff.mp (termClear block mem)).2.2.2.1
      acquireOutside := fun block mem =>
        (RegionFlow.checkTerm_eq_none_iff.mp (termClear block mem)).2.2.2.2.1
      acquireRelease := fun block mem =>
        (RegionFlow.checkTerm_eq_none_iff.mp (termClear block mem)).2.2.2.2.2.1
      leaveOutside := fun block mem =>
        (RegionFlow.checkTerm_eq_none_iff.mp (termClear block mem)).2.2.2.2.2.2.1
      leaveTyped := fun block mem =>
        (RegionFlow.checkTerm_eq_none_iff.mp (termClear block mem)).2.2.2.2.2.2.2
    }

instance [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) :
    Decidable (RegionWF alphabet flow) :=
  decidable_of_iff _ (regionWF_iff_check alphabet flow).symm

/-- An admitted region flow: its region clauses hold and its erasure is an
admitted v2 flow. -/
structure CheckedRegionFlow.{uTy, uOp} {Ty : Type uTy} [DecidableEq Ty]
    (alphabet : FlowAlphabet.{uTy, uOp} Ty) where
  flow : RegionFlow Ty
  regions : RegionWF alphabet flow
  checked : CheckedFlow alphabet
  erased : checked.erase = flow.erase

/-- Why a region flow was refused: a region clause, or a v2 clause on the erasure. -/
inductive RegionRefusal (Ty : Type uTy) where
  | region (diagnostic : RegionDiagnostic)
  | erased (diagnostic : Diagnostic Ty)
deriving DecidableEq, Repr

/-- Admit a region flow: the region clauses first, then v2 on the erasure. -/
def admitRegions [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) :
    Except (RegionRefusal Ty) (CheckedRegionFlow alphabet) :=
  match regions : flow.check alphabet with
  | some diagnostic => .error (.region diagnostic)
  | none =>
      match admitted : admit alphabet flow.erase with
      | .error diagnostic => .error (.erased diagnostic)
      | .ok checked =>
          .ok { flow := flow, regions := (regionWF_iff_check alphabet flow).mpr regions,
                checked := checked, erased := erase_admit admitted }

theorem admitRegions_ok_erase [DecidableEq Ty] {alphabet : FlowAlphabet Ty} {flow : RegionFlow Ty}
    {checked : CheckedRegionFlow alphabet} (h : admitRegions alphabet flow = .ok checked) :
    checked.flow = flow := by
  unfold admitRegions at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

end Effects
