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

/-- The region clauses of one block. -/
def checkBlock [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (block : RegionBlock Ty) : Option RegionDiagnostic :=
  let here : Option BlockId := some block.id
  match block.region with
  | some label =>
      if (flow.row? label).isNone then some ⟨.unknownLabel, here, some label⟩
      else checkTerm
  | none => checkTerm
where
  checkTerm : Option RegionDiagnostic :=
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

/-- The first failing region clause, if any. -/
def check [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) :
    Option RegionDiagnostic :=
  flow.checkTable <|>
  (match flow.block? flow.entry with
   | some entry => if entry.region.isSome then some ⟨.entryInside, some entry.id, entry.region⟩ else none
   | none => none) <|>
  flow.blocks.findSome? (flow.checkBlock alphabet)

end RegionFlow

/-- Every region clause holds. -/
def RegionWF [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) : Prop :=
  flow.check alphabet = none

instance [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) :
    Decidable (RegionWF alphabet flow) :=
  inferInstanceAs (Decidable (flow.check alphabet = none))

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
      | .ok checked => .ok { flow := flow, regions := regions, checked := checked, erased := erase_admit admitted }

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
