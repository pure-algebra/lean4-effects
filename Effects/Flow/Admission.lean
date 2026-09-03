import Effects.Flow.Raw

/-!
# Checked flow admission

This module owns the closed admission boundary. Diagnostics are produced from
one clause-indexed checker, and the checked carrier is co-located here so its
constructor can remain genuinely private while `admit` can still construct it.

Flow v2 (`test/contracts/flow-v2.contract.md`): seventeen ordered clauses over
blocks with parameter lists. Operand typing is `termTypeMismatch`; edge typing
is `argumentArity` then `argumentTypeMismatch` (positional, per successor);
variable range is `unknownVariable`; the global cycle clause is
`unchosenCycle`, decided by `cyclesChoose`.
-/

namespace Effects

/-- The fixed, public order of independently checkable admission clauses. -/
inductive AdmissionClause where
  | alphabetMismatch
  | duplicateBlockId
  | duplicateDecisionId
  | nonCanonicalBlockOrder
  | emptyRoots
  | duplicateRoot
  | nonCanonicalRootOrder
  | entryNotRoot
  | danglingRoot
  | danglingSuccessor
  | unknownOperation
  | entryTypeMismatch
  | termTypeMismatch
  | unknownVariable
  | argumentArity
  | argumentTypeMismatch
  | unchosenCycle
deriving DecidableEq, Repr

/-- Packet-owned locations for precise admission diagnostics. -/
inductive CheckSite where
  | flow
  | block (index : Nat)
  | decision (block : BlockId)
  | root (index : Nat)
  | successor (block : BlockId) (index : Nat)
  | operation (block : BlockId)
  | entry
  | term (block : BlockId)
  /-- Position `index` of the value list flowing along successor edge
  `successor` (a position in `RawTerm.successors`) of `block`; for `perform`,
  index `args.length` is the answer slot. -/
  | argument (block : BlockId) (successor index : Nat)
deriving DecidableEq, Repr

/-- Typed evidence carried by a diagnostic. -/
inductive DiagnosticPayload (Ty : Type uTy) where
  | none
  | alphabet (expected actual : AlphabetId)
  | block (id : BlockId)
  | decision (id : DecisionId)
  | operation (id : OperationId)
  | typeMismatch (expected actual : Ty)
  | variable (v : Var)
  | arity (expected actual : Nat)
deriving DecidableEq, Repr

/-- One failed admission clause, its source location, and its typed payload. -/
structure Diagnostic (Ty : Type uTy) where
  clause : AdmissionClause
  site : CheckSite
  payload : DiagnosticPayload Ty
deriving DecidableEq, Repr

/--
`failure` is the first witness of `FailureAt` in the authored source order.
The relation is generic so nested scans use the same ordering law.
-/
structure FirstFailureAt
    (source : List α)
    (FailureAt : Nat → α → β → Prop)
    (index : Nat) (item : α) (failure : β) : Prop where
  source_at : source[index]? = some item
  fails_at : FailureAt index item failure
  prior_clear : ∀ priorIndex priorItem,
    priorIndex < index →
    source[priorIndex]? = some priorItem →
    ∀ priorFailure, ¬ FailureAt priorIndex priorItem priorFailure

/-- Operand typing failures of one block (clause `termTypeMismatch`), guarded
by variable range and operation closure. -/
inductive TermFailureValid
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) : DiagnosticPayload Ty → Prop where
  | retTypeMismatch {value : Var} {actual : Ty}
      (term : block.term = .ret value)
      (typed : block.params[value.index]? = some actual)
      (mismatch : actual ≠ raw.resultTy) :
      TermFailureValid alphabet raw block (.typeMismatch raw.resultTy actual)
  | performRequestTypeMismatch {operation : OperationId} {request : Var}
      {target : BlockId} {args : List Var} {operationDef : alphabet.Op} {actual : Ty}
      (term : block.term = .perform operation request target args)
      (known : alphabet.lookup operation = some operationDef)
      (typed : block.params[request.index]? = some actual)
      (mismatch : actual ≠ alphabet.requestTy operationDef) :
      TermFailureValid alphabet raw block
        (.typeMismatch (alphabet.requestTy operationDef) actual)

/-- Positional typing failures on one successor edge of one block (clause
`argumentTypeMismatch`), guarded by resolution, arity, variable range, and
operation closure. -/
inductive ArgumentFailureValid
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) (target : BlockId) : Nat → DiagnosticPayload Ty → Prop where
  | argument {targetBlock : RawBlock Ty} {position : Nat} {argument : Var}
      {supplied declared : Ty}
      (found : lookupBlock raw target = some targetBlock)
      (argumentAt : block.term.args[position]? = some argument)
      (suppliedAt : block.params[argument.index]? = some supplied)
      (declaredAt : targetBlock.params[position]? = some declared)
      (mismatch : supplied ≠ declared) :
      ArgumentFailureValid alphabet raw block target position
        (.typeMismatch supplied declared)
  | answer {operation : OperationId} {request : Var} {args : List Var}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty} {declared : Ty}
      (term : block.term = .perform operation request target args)
      (known : alphabet.lookup operation = some operationDef)
      (found : lookupBlock raw target = some targetBlock)
      (declaredAt : targetBlock.params[args.length]? = some declared)
      (mismatch : alphabet.answerTy operationDef ≠ declared) :
      ArgumentFailureValid alphabet raw block target args.length
        (.typeMismatch (alphabet.answerTy operationDef) declared)

namespace Diagnostic

/-- A diagnostic points to the exact first source witness for its clause. -/
inductive Valid (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    Diagnostic Ty → Prop where
  | alphabetMismatch
      (mismatch : raw.alphabet ≠ alphabet.id) :
      Valid alphabet raw
        ⟨.alphabetMismatch, .flow, .alphabet alphabet.id raw.alphabet⟩
  | duplicateBlockId {index : Nat} {block : RawBlock Ty}
      (first : FirstFailureAt raw.blocks
        (fun candidateIndex candidate reported =>
          reported = candidate.id ∧
          candidate.id ∈ (raw.blocks.take candidateIndex).map RawBlock.id)
        index block block.id) :
      Valid alphabet raw ⟨.duplicateBlockId, .block index, .block block.id⟩
  | duplicateDecisionId {index : Nat} {block : RawBlock Ty}
      {decision : DecisionId}
      (first : FirstFailureAt raw.blocks
        (fun candidateIndex candidate reported =>
          ∃ (left right : BlockId) (args : List Var),
            candidate.term = .choose reported left right args ∧
            reported ∈
              (raw.blocks.take candidateIndex).filterMap
                (fun prior => RawTerm.decision? prior.term))
        index block decision) :
      Valid alphabet raw
        ⟨.duplicateDecisionId, .decision block.id, .decision decision⟩
  | nonCanonicalBlockOrder {index : Nat} {block : RawBlock Ty}
      (first : FirstFailureAt raw.blocks
        (fun candidateIndex candidate reported =>
          reported = candidate.id ∧ 0 < candidateIndex ∧
          ∃ previous,
            raw.blocks[candidateIndex - 1]? = some previous ∧
            ¬ previous.id.value < candidate.id.value)
        index block block.id) :
      Valid alphabet raw
        ⟨.nonCanonicalBlockOrder, .block index, .block block.id⟩
  | emptyRoots (empty : raw.roots = []) :
      Valid alphabet raw ⟨.emptyRoots, .flow, .none⟩
  | duplicateRoot {index : Nat} {root : BlockId}
      (first : FirstFailureAt raw.roots
        (fun candidateIndex candidate reported =>
          reported = candidate ∧ candidate ∈ raw.roots.take candidateIndex)
        index root root) :
      Valid alphabet raw ⟨.duplicateRoot, .root index, .block root⟩
  | nonCanonicalRootOrder {index : Nat} {root : BlockId}
      (first : FirstFailureAt raw.roots
        (fun candidateIndex candidate reported =>
          reported = candidate ∧ 0 < candidateIndex ∧
          ∃ previous,
            raw.roots[candidateIndex - 1]? = some previous ∧
            ¬ previous.value < candidate.value)
        index root root) :
      Valid alphabet raw
        ⟨.nonCanonicalRootOrder, .root index, .block root⟩
  | entryNotRoot (missing : raw.entry ∉ raw.roots) :
      Valid alphabet raw ⟨.entryNotRoot, .entry, .block raw.entry⟩
  | danglingRoot {index : Nat} {root : BlockId}
      (first : FirstFailureAt raw.roots
        (fun _ candidate reported =>
          reported = candidate ∧ lookupBlock raw candidate = none)
        index root root) :
      Valid alphabet raw ⟨.danglingRoot, .root index, .block root⟩
  | danglingSuccessor {blockIndex successorIndex : Nat}
      {block : RawBlock Ty} {target : BlockId}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate witness =>
          FirstFailureAt candidate.term.successors
            (fun _ successor reported =>
              reported = successor ∧ lookupBlock raw successor = none)
            witness.1 witness.2 witness.2)
        blockIndex block (successorIndex, target)) :
      Valid alphabet raw
        ⟨.danglingSuccessor, .successor block.id successorIndex, .block target⟩
  | unknownOperation {index : Nat} {block : RawBlock Ty}
      {operation : OperationId}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate reported =>
          ∃ (request : Var) (target : BlockId) (args : List Var),
            candidate.term = .perform reported request target args ∧
            alphabet.lookup reported = none)
        index block operation) :
      Valid alphabet raw
        ⟨.unknownOperation, .operation block.id, .operation operation⟩
  | entryMissing (missing : lookupBlock raw raw.entry = none) :
      Valid alphabet raw ⟨.entryTypeMismatch, .entry, .block raw.entry⟩
  | entryArity {block : RawBlock Ty}
      (found : lookupBlock raw raw.entry = some block)
      (arity : block.params.length ≠ 1) :
      Valid alphabet raw ⟨.entryTypeMismatch, .entry, .arity 1 block.params.length⟩
  | entryTypeMismatch {block : RawBlock Ty} {actual : Ty}
      (found : lookupBlock raw raw.entry = some block)
      (single : block.params = [actual])
      (mismatch : actual ≠ raw.inputTy) :
      Valid alphabet raw
        ⟨.entryTypeMismatch, .entry, .typeMismatch raw.inputTy actual⟩
  | termTypeMismatch {index : Nat} {block : RawBlock Ty}
      {payload : DiagnosticPayload Ty}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate failure =>
          TermFailureValid alphabet raw candidate failure)
        index block payload) :
      Valid alphabet raw ⟨.termTypeMismatch, .term block.id, payload⟩
  | unknownVariable {blockIndex operandIndex : Nat} {block : RawBlock Ty} {unknown : Var}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate witness =>
          FirstFailureAt candidate.term.operands
            (fun _ operand reported =>
              reported = operand ∧ candidate.params.length ≤ operand.index)
            witness.1 witness.2 witness.2)
        blockIndex block (operandIndex, unknown)) :
      Valid alphabet raw ⟨.unknownVariable, .term block.id, .variable unknown⟩
  | argumentArity {blockIndex successorIndex : Nat} {block : RawBlock Ty}
      {target : BlockId} {declared : Nat}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate witness =>
          FirstFailureAt candidate.term.successors
            (fun _ successor reported =>
              ∃ targetBlock : RawBlock Ty,
                lookupBlock raw successor = some targetBlock ∧
                targetBlock.params.length = reported ∧
                reported ≠ candidate.term.arity)
            witness.1 witness.2.1 witness.2.2)
        blockIndex block (successorIndex, target, declared)) :
      Valid alphabet raw
        ⟨.argumentArity, .successor block.id successorIndex, .arity block.term.arity declared⟩
  | argumentTypeMismatch {blockIndex successorIndex position : Nat}
      {block : RawBlock Ty} {target : BlockId} {payload : DiagnosticPayload Ty}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate witness =>
          FirstFailureAt candidate.term.successors
            (fun _ successor edge =>
              FirstFailureAt (List.range candidate.term.arity)
                (fun _ slot failure =>
                  ArgumentFailureValid alphabet raw candidate successor slot failure)
                edge.1 edge.1 edge.2)
            witness.1 witness.2.1 witness.2.2)
        blockIndex block (successorIndex, target, (position, payload))) :
      Valid alphabet raw
        ⟨.argumentTypeMismatch, .argument block.id successorIndex position, payload⟩
  | unchosenCycle {index : Nat} {block : RawBlock Ty}
      (first : FirstFailureAt raw.blocks
        (fun _ candidate reported =>
          reported = candidate.id ∧
          ∃ next : BlockId,
            EdgeNoChoose raw candidate.id next ∧ ReachableNoChoose raw next candidate.id)
        index block block.id) :
      Valid alphabet raw ⟨.unchosenCycle, .block index, .block block.id⟩

end Diagnostic

/-- The exhaustive first-error scan order. -/
def scan : List AdmissionClause := [
  .alphabetMismatch,
  .duplicateBlockId,
  .duplicateDecisionId,
  .nonCanonicalBlockOrder,
  .emptyRoots,
  .duplicateRoot,
  .nonCanonicalRootOrder,
  .entryNotRoot,
  .danglingRoot,
  .danglingSuccessor,
  .unknownOperation,
  .entryTypeMismatch,
  .termTypeMismatch,
  .unknownVariable,
  .argumentArity,
  .argumentTypeMismatch,
  .unchosenCycle
]

private def localDecisionIds (raw : RawFlow Ty) : List DecisionId :=
  raw.blocks.filterMap fun block => block.term.decision?

private theorem idsWF_view (raw : RawFlow Ty) :
    IdsWF raw ↔
      (raw.blocks.map RawBlock.id).Nodup ∧
      raw.blocks.Pairwise
        (fun left right => left.id.value < right.id.value) ∧
      (localDecisionIds raw).Nodup := by
  rfl

private def localEntryWFDecidable [DecidableEq Ty]
    (raw : RawFlow Ty) : Decidable (EntryWF raw) := by
  unfold EntryWF
  split <;> infer_instance

/-- The proposition checked by one diagnostic clause. -/
private def ClauseHolds
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    AdmissionClause → Prop
  | .alphabetMismatch => AlphabetWF alphabet raw
  | .duplicateBlockId => (raw.blocks.map RawBlock.id).Nodup
  | .duplicateDecisionId => (localDecisionIds raw).Nodup
  | .nonCanonicalBlockOrder =>
      raw.blocks.Pairwise
        (fun left right => left.id.value < right.id.value)
  | .emptyRoots => raw.roots ≠ []
  | .duplicateRoot => raw.roots.Nodup
  | .nonCanonicalRootOrder =>
      raw.roots.Pairwise (fun left right => left.value < right.value)
  | .entryNotRoot => raw.entry ∈ raw.roots
  | .danglingRoot =>
      ∀ root, root ∈ raw.roots → (lookupBlock raw root).isSome = true
  | .danglingSuccessor => ReferencesWF raw
  | .unknownOperation => OperationsWF alphabet raw
  | .entryTypeMismatch => EntryWF raw
  | .termTypeMismatch =>
      ∀ block, block ∈ raw.blocks → OperandsWF alphabet raw block
  | .unknownVariable => ∀ block, block ∈ raw.blocks → block.VarsWF
  | .argumentArity => ∀ block, block ∈ raw.blocks → ArityWF raw block
  | .argumentTypeMismatch =>
      ∀ block, block ∈ raw.blocks → ArgumentsWF alphabet raw block
  | .unchosenCycle => CyclesWF raw

/-- Run one indexed source-order scan and retain the exact source item. -/
private def firstFailure?
    (source : List α) (check : Nat → α → Option β) :
    Option (Nat × α × β) :=
  source.zipIdx.findSome? fun (item, index) =>
    (check index item).map fun failure => (index, item, failure)

private theorem firstFailure?_eq_none_iff
    {source : List α} {check : Nat → α → Option β} :
    firstFailure? source check = none ↔
      ∀ index item, source[index]? = some item → check index item = none := by
  simp only [firstFailure?, List.findSome?_eq_none_iff]
  constructor
  · intro clear index item sourceAt
    have member : (item, index) ∈ source.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr sourceAt
    have mapped := clear (item, index) member
    simpa using mapped
  · intro clear pair member
    rcases pair with ⟨item, index⟩
    have sourceAt : source[index]? = some item :=
      List.mk_mem_zipIdx_iff_getElem?.mp member
    have checked := clear index item sourceAt
    simp [checked]

private theorem firstFailure?_eq_some_valid
    {source : List α} {check : Nat → α → Option β}
    {FailureAt : Nat → α → β → Prop}
    (precise : ∀ index item failure,
      check index item = some failure ↔ FailureAt index item failure)
    {index : Nat} {item : α} {failure : β}
    (found : firstFailure? source check = some (index, item, failure)) :
    FirstFailureAt source FailureAt index item failure := by
  simp only [firstFailure?] at found
  obtain ⟨before, pair, after, split, atPair, prior⟩ :=
    List.findSome?_eq_some_iff.mp found
  rcases pair with ⟨foundItem, foundIndex⟩
  simp only [Option.map_eq_some_iff] at atPair
  obtain ⟨foundFailure, checkFound, tripleEq⟩ := atPair
  cases tripleEq
  have pairMember : (item, index) ∈ source.zipIdx := by
    rw [split]
    simp
  have sourceAt : source[index]? = some item :=
    List.mk_mem_zipIdx_iff_getElem?.mp pairMember
  refine {
    source_at := sourceAt
    fails_at := (precise index item failure).mp checkFound
    prior_clear := ?_
  }
  intro priorIndex priorItem priorLt priorAt priorFailure priorFails
  have currentAtPosition :
      (source.zipIdx)[before.length]? = some (item, index) := by
    rw [split]
    simp
  rw [List.getElem?_zipIdx] at currentAtPosition
  cases sourceEq : source[before.length]? with
  | none => simp [sourceEq] at currentAtPosition
  | some currentItem =>
    simp [sourceEq] at currentAtPosition
    have indexEq : index = before.length := currentAtPosition.2.symm
    have priorPairAt :
        (source.zipIdx)[priorIndex]? = some (priorItem, priorIndex) := by
      simp [List.getElem?_zipIdx, priorAt]
    have priorBeforeAt : before[priorIndex]? = some (priorItem, priorIndex) := by
      rw [split] at priorPairAt
      rw [List.getElem?_append_left (by omega)] at priorPairAt
      exact priorPairAt
    have priorMember : (priorItem, priorIndex) ∈ before :=
      List.mem_iff_getElem?.mpr ⟨priorIndex, priorBeforeAt⟩
    have clearMapped := prior (priorItem, priorIndex) priorMember
    have clear : check priorIndex priorItem = none := by
      simpa using clearMapped
    have failedCheck : check priorIndex priorItem = some priorFailure :=
      (precise priorIndex priorItem priorFailure).mpr priorFails
    rw [clear] at failedCheck
    contradiction

private theorem firstFailure?_eq_some_iff
    {source : List α} {check : Nat → α → Option β}
    {FailureAt : Nat → α → β → Prop}
    (precise : ∀ index item failure,
      check index item = some failure ↔ FailureAt index item failure)
    {index : Nat} {item : α} {failure : β} :
    firstFailure? source check = some (index, item, failure) ↔
      FirstFailureAt source FailureAt index item failure := by
  constructor
  · exact firstFailure?_eq_some_valid precise
  · intro expected
    cases resultEq : firstFailure? source check with
    | none =>
        have clear := firstFailure?_eq_none_iff.mp resultEq
        have checkedClear := clear index item expected.source_at
        have checkedFailure :=
          (precise index item failure).mpr expected.fails_at
        rw [checkedClear] at checkedFailure
        contradiction
    | some result =>
        rcases result with ⟨foundIndex, foundItem, foundFailure⟩
        have found := firstFailure?_eq_some_valid precise resultEq
        have indexEq : foundIndex = index := by
          rcases Nat.lt_trichotomy foundIndex index with earlier | equalOrLater
          · exact (expected.prior_clear foundIndex foundItem earlier
              found.source_at foundFailure found.fails_at).elim
          · rcases equalOrLater with equal | later
            · exact equal
            · exact (found.prior_clear index item later expected.source_at
                failure expected.fails_at).elim
        subst foundIndex
        have itemEq : foundItem = item := by
          have expectedAt := expected.source_at
          rw [found.source_at] at expectedAt
          exact Option.some.inj expectedAt
        subst foundItem
        have foundCheck : check index item = some foundFailure :=
          (precise index item foundFailure).mpr found.fails_at
        have expectedCheck : check index item = some failure :=
          (precise index item failure).mpr expected.fails_at
        have failureEq : foundFailure = failure :=
          Option.some.inj (foundCheck.symm.trans expectedCheck)
        subst foundFailure
        rfl

private theorem nodup_of_no_prefix_duplicate [DecidableEq α]
    (source : List α)
    (clear : ∀ index item,
      source[index]? = some item → item ∉ source.take index) :
    source.Nodup := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons]
      constructor
      · intro headMem
        obtain ⟨index, headAt⟩ := List.mem_iff_getElem?.mp headMem
        have noDuplicate := clear (index + 1) head (by simp [headAt])
        exact noDuplicate (by simp)
      · apply ih
        intro index item itemAt itemMem
        have noDuplicate := clear (index + 1) item (by simp [itemAt])
        exact noDuplicate (by simp [itemMem])

private theorem map_nodup_of_no_prefix_duplicate [DecidableEq β]
    (source : List α) (key : α → β)
    (clear : ∀ index item,
      source[index]? = some item →
      key item ∉ (source.take index).map key) :
    (source.map key).Nodup := by
  apply nodup_of_no_prefix_duplicate
  intro index item mappedAt mappedMem
  rw [List.getElem?_map] at mappedAt
  cases sourceAt : source[index]? with
  | none => simp [sourceAt] at mappedAt
  | some sourceItem =>
      simp [sourceAt] at mappedAt
      subst item
      exact clear index sourceItem sourceAt (by simpa using mappedMem)

private theorem filterMap_nodup_of_no_prefix_duplicate [DecidableEq β]
    (source : List α) (pick : α → Option β)
    (clear : ∀ index item,
      source[index]? = some item →
      ∀ value, pick item = some value →
        value ∉ (source.take index).filterMap pick) :
    (source.filterMap pick).Nodup := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      cases headEq : pick head with
      | none =>
          simp only [List.filterMap_cons, headEq]
          apply ih
          intro index item itemAt value picked valueMem
          have noDuplicate := clear (index + 1) item (by simp [itemAt])
            value picked
          exact noDuplicate (by simp [headEq, valueMem])
      | some headValue =>
          simp only [List.filterMap_cons, headEq, List.nodup_cons]
          constructor
          · intro headValueMem
            simp only [List.mem_filterMap] at headValueMem
            obtain ⟨item, itemMem, picked⟩ := headValueMem
            obtain ⟨index, itemAt⟩ := List.mem_iff_getElem?.mp itemMem
            have noDuplicate := clear (index + 1) item (by simp [itemAt])
              headValue picked
            exact noDuplicate (by simp [headEq])
          · apply ih
            intro index item itemAt value picked valueMem
            have noDuplicate := clear (index + 1) item (by simp [itemAt])
              value picked
            exact noDuplicate (by simp [headEq, valueMem])

private theorem pairwise_nat_of_adjacent
    (source : List α) (value : α → Nat)
    (adjacent : ∀ index item previous,
      0 < index →
      source[index]? = some item →
      source[index - 1]? = some previous →
      value previous < value item) :
    source.Pairwise (fun left right => value left < value right) := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      have tailAdjacent : ∀ index item previous,
          0 < index →
          tail[index]? = some item →
          tail[index - 1]? = some previous →
          value previous < value item := by
        intro index item previous positive itemAt previousAt
        cases index with
        | zero => omega
        | succ prior =>
            exact adjacent (prior + 2) item previous (by omega)
              (by simp [itemAt]) (by simpa using previousAt)
      have tailPairwise := ih tailAdjacent
      rw [List.pairwise_cons]
      refine ⟨?_, tailPairwise⟩
      intro item itemMem
      cases tail with
      | nil => contradiction
      | cons first rest =>
          have headFirst : value head < value first :=
            adjacent 1 first head (by omega) (by simp) (by simp)
          simp only [List.mem_cons] at itemMem
          rcases itemMem with rfl | itemMem
          · exact headFirst
          · exact Nat.lt_trans headFirst
              (List.rel_of_pairwise_cons tailPairwise itemMem)

private def duplicateBlockFailure? (raw : RawFlow Ty)
    (index : Nat) (block : RawBlock Ty) : Option BlockId :=
  if block.id ∈ (raw.blocks.take index).map RawBlock.id then
    some block.id
  else
    none

private theorem duplicateBlockFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (block : RawBlock Ty)
    (reported : BlockId) :
    duplicateBlockFailure? raw index block = some reported ↔
      reported = block.id ∧
      block.id ∈ (raw.blocks.take index).map RawBlock.id := by
  simp [duplicateBlockFailure?, and_comm, eq_comm]

private def duplicateDecisionFailure? (raw : RawFlow Ty)
    (index : Nat) (block : RawBlock Ty) : Option DecisionId :=
  match block.term with
  | .choose decision _ _ _ =>
      if decision ∈ (raw.blocks.take index).filterMap (fun prior => prior.term.decision?) then
        some decision
      else
        none
  | _ => none

private theorem duplicateDecisionFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (block : RawBlock Ty)
    (reported : DecisionId) :
    duplicateDecisionFailure? raw index block = some reported ↔
      ∃ (left right : BlockId) (args : List Var),
        block.term = .choose reported left right args ∧
        reported ∈
          (raw.blocks.take index).filterMap (fun prior => prior.term.decision?) := by
  cases termEq : block.term with
  | ret | jump | perform => simp [duplicateDecisionFailure?, termEq]
  | choose decision left right args =>
      by_cases member : decision ∈
          (raw.blocks.take index).filterMap (fun prior => prior.term.decision?)
      · simp only [duplicateDecisionFailure?, termEq, member, ↓reduceIte, Option.some.injEq]
        constructor
        · intro reportedEq
          subst reported
          exact ⟨left, right, args, rfl, member⟩
        · rintro ⟨_, _, _, chooseEq, _⟩
          exact (RawTerm.choose.inj chooseEq).1
      · have noFailure : duplicateDecisionFailure? raw index block = none := by
          simp [duplicateDecisionFailure?, termEq, member]
        rw [noFailure]
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨_, _, _, chooseEq, reportedMem⟩
          obtain ⟨decisionEq, -, -, -⟩ := RawTerm.choose.inj chooseEq
          subst decisionEq
          exact (member reportedMem).elim

private def orderFailure? (source : List α) (value : α → Nat)
    (index : Nat) (item : α) : Option α :=
  match index with
  | 0 => none
  | prior + 1 =>
      match source[prior]? with
      | none => none
      | some previous =>
          if value previous < value item then none else some item

private theorem orderFailure?_eq_some_iff
    (source : List α) (value : α → Nat)
    (index : Nat) (item reported : α) :
    orderFailure? source value index item = some reported ↔
      reported = item ∧ 0 < index ∧
      ∃ previous,
        source[index - 1]? = some previous ∧
        ¬ value previous < value item := by
  cases index with
  | zero => simp [orderFailure?]
  | succ prior =>
      cases previousEq : source[prior]? with
      | none => simp [orderFailure?, previousEq]
      | some previous =>
          by_cases ordered : value previous < value item
          · simp [orderFailure?, previousEq, ordered]
          · simp [orderFailure?, previousEq, ordered, eq_comm, Nat.not_lt]
            omega

private def duplicateRootFailure? (raw : RawFlow Ty)
    (index : Nat) (root : BlockId) : Option BlockId :=
  if root ∈ raw.roots.take index then some root else none

private theorem duplicateRootFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (root reported : BlockId) :
    duplicateRootFailure? raw index root = some reported ↔
      reported = root ∧ root ∈ raw.roots.take index := by
  simp [duplicateRootFailure?, and_comm, eq_comm]

private def danglingRootFailure? (raw : RawFlow Ty)
    (_ : Nat) (root : BlockId) : Option BlockId :=
  match lookupBlock raw root with
  | none => some root
  | some _ => none

private theorem danglingRootFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (root reported : BlockId) :
    danglingRootFailure? raw index root = some reported ↔
      reported = root ∧ lookupBlock raw root = none := by
  cases found : lookupBlock raw root <;>
    simp [danglingRootFailure?, found, eq_comm]

private def danglingSuccessorFailure? (raw : RawFlow Ty)
    (_ : Nat) (target : BlockId) : Option BlockId :=
  match lookupBlock raw target with
  | none => some target
  | some _ => none

private theorem danglingSuccessorFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (target reported : BlockId) :
    danglingSuccessorFailure? raw index target = some reported ↔
      reported = target ∧ lookupBlock raw target = none := by
  cases found : lookupBlock raw target <;>
    simp [danglingSuccessorFailure?, found, eq_comm]

private def firstPreciseDanglingSuccessorIn? (raw : RawFlow Ty)
    (block : RawBlock Ty) : Option (Nat × BlockId × BlockId) :=
  firstFailure? block.term.successors (danglingSuccessorFailure? raw)

private theorem firstPreciseDanglingSuccessorIn?_eq_some_valid
    {raw : RawFlow Ty} {block : RawBlock Ty}
    {index : Nat} {target reported : BlockId}
    (found : firstPreciseDanglingSuccessorIn? raw block =
      some (index, target, reported)) :
    FirstFailureAt block.term.successors
      (fun _ successor witness =>
        witness = successor ∧ lookupBlock raw successor = none)
      index target reported := by
  exact firstFailure?_eq_some_valid
    (danglingSuccessorFailure?_eq_some_iff raw) found

private def danglingBlockFailure? (raw : RawFlow Ty)
    (_ : Nat) (block : RawBlock Ty) : Option (Nat × BlockId) :=
  match firstPreciseDanglingSuccessorIn? raw block with
  | none => none
  | some (index, target, _) => some (index, target)

private theorem danglingBlockFailure?_eq_some_iff
    (raw : RawFlow Ty) (index : Nat) (block : RawBlock Ty)
    (witness : Nat × BlockId) :
    danglingBlockFailure? raw index block = some witness ↔
      FirstFailureAt block.term.successors
        (fun _ successor reported =>
          reported = successor ∧ lookupBlock raw successor = none)
        witness.1 witness.2 witness.2 := by
  constructor
  · intro found
    unfold danglingBlockFailure? at found
    cases innerEq : firstPreciseDanglingSuccessorIn? raw block with
    | none => simp [innerEq] at found
    | some result =>
        rcases result with ⟨successorIndex, target, reported⟩
        simp [innerEq] at found
        obtain ⟨rfl, rfl⟩ := found
        have valid := firstPreciseDanglingSuccessorIn?_eq_some_valid innerEq
        have reportedEq : reported = target := valid.fails_at.1
        subst reported
        exact valid
  · intro valid
    unfold danglingBlockFailure?
    have innerEq : firstPreciseDanglingSuccessorIn? raw block =
        some (witness.1, witness.2, witness.2) :=
      firstFailure?_eq_some_iff
        (danglingSuccessorFailure?_eq_some_iff raw) |>.mpr valid
    simp [innerEq]

private def unknownOperationFailure? (alphabet : FlowAlphabet Ty)
    (_ : Nat) (block : RawBlock Ty) : Option OperationId :=
  match block.term with
  | .perform operation _ _ _ =>
      match alphabet.lookup operation with
      | none => some operation
      | some _ => none
  | _ => none

private theorem unknownOperationFailure?_eq_some_iff
    (alphabet : FlowAlphabet Ty) (index : Nat) (block : RawBlock Ty)
    (reported : OperationId) :
    unknownOperationFailure? alphabet index block = some reported ↔
      ∃ (request : Var) (target : BlockId) (args : List Var),
        block.term = .perform reported request target args ∧
        alphabet.lookup reported = none := by
  cases termEq : block.term with
  | ret | jump | choose => simp [unknownOperationFailure?, termEq]
  | perform operation request target args =>
      cases found : alphabet.lookup operation with
      | none =>
          constructor
          · intro failure
            simp [unknownOperationFailure?, termEq, found] at failure
            subst reported
            exact ⟨request, target, args, rfl, found⟩
          · rintro ⟨_, _, _, sameTerm, unknown⟩
            injection sameTerm with operationEq
            subst operationEq
            simp [unknownOperationFailure?, termEq, found]
      | some operationDef =>
          constructor
          · intro failure
            simp [unknownOperationFailure?, termEq, found] at failure
          · rintro ⟨_, _, _, sameTerm, unknown⟩
            injection sameTerm with operationEq
            subst operationEq
            rw [found] at unknown
            contradiction

private theorem unknownOperationFailure?_eq_none_iff
    (alphabet : FlowAlphabet Ty) (index : Nat) (block : RawBlock Ty) :
    unknownOperationFailure? alphabet index block = none ↔ OperationWF alphabet block := by
  cases termEq : block.term with
  | ret | jump | choose => simp [unknownOperationFailure?, OperationWF, termEq]
  | perform operation request target args =>
      cases found : alphabet.lookup operation <;>
        simp [unknownOperationFailure?, OperationWF, termEq, found]

/-! ## Operand typing (`termTypeMismatch`) -/

private def operandFailure? [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) : Option (DiagnosticPayload Ty) :=
  match block.term with
  | .ret value =>
      match block.params[value.index]? with
      | some actual =>
          if actual = raw.resultTy then none
          else some (.typeMismatch raw.resultTy actual)
      | none => none
  | .perform operation request _ _ =>
      match alphabet.lookup operation, block.params[request.index]? with
      | some operationDef, some actual =>
          if actual = alphabet.requestTy operationDef then none
          else some (.typeMismatch (alphabet.requestTy operationDef) actual)
      | _, _ => none
  | _ => none

private theorem operandFailure?_eq_some_iff [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) (payload : DiagnosticPayload Ty) :
    operandFailure? alphabet raw block = some payload ↔
      TermFailureValid alphabet raw block payload := by
  constructor
  · intro failure
    cases termEq : block.term with
    | ret value =>
        cases typedEq : block.params[value.index]? with
        | none => simp [operandFailure?, termEq, typedEq] at failure
        | some actual =>
            by_cases typed : actual = raw.resultTy
            · simp [operandFailure?, termEq, typedEq, typed] at failure
            · simp [operandFailure?, termEq, typedEq, typed] at failure
              subst payload
              exact .retTypeMismatch termEq typedEq typed
    | jump target args => simp [operandFailure?, termEq] at failure
    | choose decision left right args => simp [operandFailure?, termEq] at failure
    | perform operation request target args =>
        cases operationEq : alphabet.lookup operation with
        | none => simp [operandFailure?, termEq, operationEq] at failure
        | some operationDef =>
            cases typedEq : block.params[request.index]? with
            | none => simp [operandFailure?, termEq, operationEq, typedEq] at failure
            | some actual =>
                by_cases typed : actual = alphabet.requestTy operationDef
                · simp [operandFailure?, termEq, operationEq, typedEq, typed] at failure
                · simp [operandFailure?, termEq, operationEq, typedEq, typed] at failure
                  subst payload
                  exact .performRequestTypeMismatch termEq operationEq typedEq typed
  · intro valid
    cases valid with
    | retTypeMismatch term typed mismatch =>
        simp [operandFailure?, term, typed, mismatch]
    | performRequestTypeMismatch term known typed mismatch =>
        simp [operandFailure?, term, known, typed, mismatch]

private theorem operandFailure?_eq_none_iff [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) :
    operandFailure? alphabet raw block = none ↔
      OperandsWF alphabet raw block := by
  cases termEq : block.term with
  | ret value =>
      cases typedEq : block.params[value.index]? with
      | none => simp [operandFailure?, OperandsWF, termEq, typedEq]
      | some actual =>
          by_cases typed : actual = raw.resultTy <;>
            simp [operandFailure?, OperandsWF, termEq, typedEq, typed]
  | jump target args => simp [operandFailure?, OperandsWF, termEq]
  | choose decision left right args => simp [operandFailure?, OperandsWF, termEq]
  | perform operation request target args =>
      cases operationEq : alphabet.lookup operation with
      | none =>
          cases typedEq : block.params[request.index]? <;>
            simp [operandFailure?, OperandsWF, termEq, operationEq, typedEq]
      | some operationDef =>
          cases typedEq : block.params[request.index]? with
          | none => simp [operandFailure?, OperandsWF, termEq, operationEq, typedEq]
          | some actual =>
              by_cases typed : actual = alphabet.requestTy operationDef <;>
                simp [operandFailure?, OperandsWF, termEq, operationEq, typedEq, typed]

/-! ## Variable range (`unknownVariable`) -/

private def variableFailure? (block : RawBlock Ty) (_ : Nat) (operand : Var) : Option Var :=
  if block.params.length ≤ operand.index then some operand else none

private theorem variableFailure?_eq_some_iff (block : RawBlock Ty) (index : Nat)
    (operand reported : Var) :
    variableFailure? block index operand = some reported ↔
      reported = operand ∧ block.params.length ≤ operand.index := by
  simp [variableFailure?, and_comm, eq_comm]

private def variableBlockFailure? (_ : Nat) (block : RawBlock Ty) : Option (Nat × Var) :=
  match firstFailure? block.term.operands (variableFailure? block) with
  | none => none
  | some (index, _, reported) => some (index, reported)

private theorem variableBlockFailure?_eq_some_iff (index : Nat) (block : RawBlock Ty)
    (witness : Nat × Var) :
    variableBlockFailure? index block = some witness ↔
      FirstFailureAt block.term.operands
        (fun _ operand reported =>
          reported = operand ∧ block.params.length ≤ operand.index)
        witness.1 witness.2 witness.2 := by
  constructor
  · intro found
    unfold variableBlockFailure? at found
    cases innerEq : firstFailure? block.term.operands (variableFailure? block) with
    | none => simp [innerEq] at found
    | some result =>
        rcases result with ⟨operandIndex, operand, reported⟩
        simp [innerEq] at found
        obtain ⟨rfl, rfl⟩ := found
        have valid := firstFailure?_eq_some_valid (variableFailure?_eq_some_iff block) innerEq
        have reportedEq : reported = operand := valid.fails_at.1
        subst reported
        exact valid
  · intro valid
    unfold variableBlockFailure?
    have innerEq : firstFailure? block.term.operands (variableFailure? block) =
        some (witness.1, witness.2, witness.2) :=
      (firstFailure?_eq_some_iff (variableFailure?_eq_some_iff block)).mpr valid
    simp [innerEq]

private theorem variableBlockFailure?_eq_none_iff (index : Nat) (block : RawBlock Ty) :
    variableBlockFailure? index block = none ↔ block.VarsWF := by
  unfold variableBlockFailure?
  cases innerEq : firstFailure? block.term.operands (variableFailure? block) with
  | some result =>
      rcases result with ⟨operandIndex, operand, reported⟩
      simp only [reduceCtorEq, false_iff]
      intro wf
      have valid := firstFailure?_eq_some_valid (variableFailure?_eq_some_iff block) innerEq
      have inRange := wf operand (List.mem_iff_getElem?.mpr ⟨operandIndex, valid.source_at⟩)
      exact absurd valid.fails_at.2 (Nat.not_le.mpr inRange)
  | none =>
      simp only [true_iff]
      intro operand operandMem
      obtain ⟨operandIndex, operandAt⟩ := List.mem_iff_getElem?.mp operandMem
      have clear := firstFailure?_eq_none_iff.mp innerEq operandIndex operand operandAt
      apply Decidable.byContradiction
      intro outOfRange
      have failed : variableFailure? block operandIndex operand = some operand :=
        (variableFailure?_eq_some_iff block operandIndex operand operand).mpr
          ⟨rfl, Nat.not_lt.mp outOfRange⟩
      rw [clear] at failed
      contradiction

/-! ## Successor arity (`argumentArity`) -/

private def arityFailure? (raw : RawFlow Ty) (block : RawBlock Ty)
    (_ : Nat) (target : BlockId) : Option Nat :=
  match lookupBlock raw target with
  | none => none
  | some targetBlock =>
      if targetBlock.params.length = block.term.arity then none
      else some targetBlock.params.length

private theorem arityFailure?_eq_some_iff (raw : RawFlow Ty) (block : RawBlock Ty)
    (index : Nat) (target : BlockId) (reported : Nat) :
    arityFailure? raw block index target = some reported ↔
      ∃ targetBlock : RawBlock Ty,
        lookupBlock raw target = some targetBlock ∧
        targetBlock.params.length = reported ∧
        reported ≠ block.term.arity := by
  cases found : lookupBlock raw target with
  | none => simp [arityFailure?, found]
  | some targetBlock =>
      by_cases matched : targetBlock.params.length = block.term.arity
      · constructor
        · intro failure
          simp [arityFailure?, found, matched] at failure
        · rintro ⟨candidate, candidateEq, lengthEq, mismatch⟩
          obtain rfl := Option.some.inj candidateEq
          exact absurd (lengthEq.symm.trans matched) mismatch
      · simp only [arityFailure?, found, matched, ↓reduceIte, Option.some.injEq]
        constructor
        · intro lengthEq
          exact ⟨targetBlock, rfl, lengthEq, fun eq => matched (lengthEq.trans eq)⟩
        · rintro ⟨_, rfl, lengthEq, _⟩
          exact lengthEq

private def arityBlockFailure? (raw : RawFlow Ty) (_ : Nat) (block : RawBlock Ty) :
    Option (Nat × BlockId × Nat) :=
  firstFailure? block.term.successors (arityFailure? raw block)

private theorem arityBlockFailure?_eq_some_iff (raw : RawFlow Ty) (index : Nat)
    (block : RawBlock Ty) (witness : Nat × BlockId × Nat) :
    arityBlockFailure? raw index block = some witness ↔
      FirstFailureAt block.term.successors
        (fun _ successor reported =>
          ∃ targetBlock : RawBlock Ty,
            lookupBlock raw successor = some targetBlock ∧
            targetBlock.params.length = reported ∧
            reported ≠ block.term.arity)
        witness.1 witness.2.1 witness.2.2 := by
  rcases witness with ⟨successorIndex, target, declared⟩
  exact firstFailure?_eq_some_iff (arityFailure?_eq_some_iff raw block)

private theorem arityBlockFailure?_eq_none_iff (raw : RawFlow Ty) (index : Nat)
    (block : RawBlock Ty) :
    arityBlockFailure? raw index block = none ↔ ArityWF raw block := by
  unfold arityBlockFailure?
  rw [firstFailure?_eq_none_iff]
  constructor
  · intro clear target targetMem
    obtain ⟨successorIndex, targetAt⟩ := List.mem_iff_getElem?.mp targetMem
    have checked := clear successorIndex target targetAt
    cases found : lookupBlock raw target with
    | none => simp
    | some targetBlock =>
        simp only
        apply Decidable.byContradiction
        intro mismatch
        have failed := (arityFailure?_eq_some_iff raw block successorIndex target
          targetBlock.params.length).mpr ⟨targetBlock, found, rfl, mismatch⟩
        rw [checked] at failed
        contradiction
  · intro wf successorIndex target targetAt
    have localWF := wf target (List.mem_iff_getElem?.mpr ⟨successorIndex, targetAt⟩)
    cases found : lookupBlock raw target with
    | none => simp [arityFailure?, found]
    | some targetBlock =>
        simp only [found] at localWF
        simp [arityFailure?, found, localWF]

/-! ## Argument and answer typing (`argumentTypeMismatch`) -/

private def slotFailure? [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) (target : BlockId) (slot : Nat) : Option (DiagnosticPayload Ty) :=
  match lookupBlock raw target with
  | none => none
  | some targetBlock =>
    match block.term.args[slot]? with
    | some argument =>
        match block.params[argument.index]?, targetBlock.params[slot]? with
        | some supplied, some declared =>
            if supplied = declared then none else some (.typeMismatch supplied declared)
        | _, _ => none
    | none =>
        match block.term with
        | .perform operation _ performTarget args =>
            if slot = args.length ∧ performTarget = target then
              match alphabet.lookup operation, targetBlock.params[slot]? with
              | some operationDef, some declared =>
                  if alphabet.answerTy operationDef = declared then none
                  else some (.typeMismatch (alphabet.answerTy operationDef) declared)
              | _, _ => none
            else none
        | _ => none

private theorem slotFailure?_eq_some_iff [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (block : RawBlock Ty) (target : BlockId) (slot : Nat)
    (payload : DiagnosticPayload Ty) :
    slotFailure? alphabet raw block target slot = some payload ↔
      ArgumentFailureValid alphabet raw block target slot payload := by
  constructor
  · intro failure
    cases found : lookupBlock raw target with
    | none => simp [slotFailure?, found] at failure
    | some targetBlock =>
        cases argumentAt : block.term.args[slot]? with
        | some argument =>
            cases suppliedAt : block.params[argument.index]? with
            | none => simp [slotFailure?, found, argumentAt, suppliedAt] at failure
            | some supplied =>
                cases declaredAt : targetBlock.params[slot]? with
                | none => simp [slotFailure?, found, argumentAt, suppliedAt, declaredAt] at failure
                | some declared =>
                    by_cases typed : supplied = declared
                    · simp [slotFailure?, found, argumentAt, suppliedAt, declaredAt, typed] at failure
                    · simp [slotFailure?, found, argumentAt, suppliedAt, declaredAt, typed] at failure
                      subst payload
                      exact .argument found argumentAt suppliedAt declaredAt typed
        | none =>
            simp only [slotFailure?, found, argumentAt] at failure
            cases termEq : block.term with
            | ret value => simp [termEq] at failure
            | jump jumpTarget args => simp [termEq] at failure
            | choose decision left right args => simp [termEq] at failure
            | perform operation request performTarget args =>
                by_cases answerSlot : slot = args.length ∧ performTarget = target
                · obtain ⟨slotEq, targetEq⟩ := answerSlot
                  subst slotEq
                  subst targetEq
                  cases known : alphabet.lookup operation with
                  | none => simp [termEq, known] at failure
                  | some operationDef =>
                      cases declaredAt : targetBlock.params[args.length]? with
                      | none => simp [termEq, known, declaredAt] at failure
                      | some declared =>
                          by_cases typed : alphabet.answerTy operationDef = declared
                          · simp [termEq, known, declaredAt, typed] at failure
                          · simp [termEq, known, declaredAt, typed] at failure
                            subst payload
                            exact .answer termEq known found declaredAt typed
                · simp [termEq, answerSlot] at failure
  · intro valid
    cases valid with
    | argument found argumentAt suppliedAt declaredAt mismatch =>
        simp [slotFailure?, found, argumentAt, suppliedAt, declaredAt, mismatch]
    | @answer operation request args operationDef targetBlock declared term known found declaredAt mismatch =>
        have argumentAt : block.term.args[args.length]? = none := by
          rw [term]
          exact List.getElem?_eq_none (Nat.le_refl _)
        simp only [slotFailure?, found, argumentAt]
        simp [term, known, declaredAt, mismatch]

private theorem slotFailure?_eq_none_iff [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (block : RawBlock Ty) (target : BlockId) (slot : Nat) :
    slotFailure? alphabet raw block target slot = none ↔
      SlotWF alphabet raw block target slot := by
  cases found : lookupBlock raw target with
  | none => simp [slotFailure?, SlotWF, found]
  | some targetBlock =>
      cases argumentAt : block.term.args[slot]? with
      | some argument =>
          cases suppliedAt : block.params[argument.index]? with
          | none => simp [slotFailure?, SlotWF, found, argumentAt, suppliedAt]
          | some supplied =>
              cases declaredAt : targetBlock.params[slot]? with
              | none => simp [slotFailure?, SlotWF, found, argumentAt, suppliedAt, declaredAt]
              | some declared =>
                  by_cases typed : supplied = declared <;>
                    simp [slotFailure?, SlotWF, found, argumentAt, suppliedAt, declaredAt, typed]
      | none =>
          simp only [slotFailure?, SlotWF, found, argumentAt]
          cases block.term with
          | ret value => simp
          | jump jumpTarget args => simp
          | choose decision left right args => simp
          | perform operation request performTarget args =>
              by_cases slotEq : slot = args.length
              · by_cases targetEq : performTarget = target
                · subst slotEq
                  subst targetEq
                  cases known : alphabet.lookup operation with
                  | none => simp [known]
                  | some operationDef =>
                      cases targetBlock.params[args.length]? with
                      | none => simp [known]
                      | some declared =>
                          by_cases typed : alphabet.answerTy operationDef = declared <;>
                            simp [known, typed]
                · subst slotEq
                  simp [targetEq]
              · simp [slotEq]

private theorem range_getElem?_eq {n index item : Nat}
    (at_ : (List.range n)[index]? = some item) : item = index := by
  have lt : index < n := by
    have := List.getElem?_eq_some_iff.mp at_
    obtain ⟨h, _⟩ := this
    simpa using h
  rw [List.getElem?_range lt] at at_
  exact (Option.some.inj at_).symm

private def edgeFailure? [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) (_ : Nat) (target : BlockId) : Option (Nat × DiagnosticPayload Ty) :=
  match firstFailure? (List.range block.term.arity)
      (fun _ slot => slotFailure? alphabet raw block target slot) with
  | none => none
  | some (position, _, payload) => some (position, payload)

private theorem edgeFailure?_eq_some_iff [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (block : RawBlock Ty) (index : Nat) (target : BlockId)
    (edge : Nat × DiagnosticPayload Ty) :
    edgeFailure? alphabet raw block index target = some edge ↔
      FirstFailureAt (List.range block.term.arity)
        (fun _ slot failure => ArgumentFailureValid alphabet raw block target slot failure)
        edge.1 edge.1 edge.2 := by
  constructor
  · intro found
    unfold edgeFailure? at found
    cases innerEq : firstFailure? (List.range block.term.arity)
        (fun _ slot => slotFailure? alphabet raw block target slot) with
    | none => simp [innerEq] at found
    | some result =>
        rcases result with ⟨position, slot, payload⟩
        simp [innerEq] at found
        obtain ⟨rfl, rfl⟩ := found
        have valid := firstFailure?_eq_some_valid
          (fun _ slot failure => slotFailure?_eq_some_iff alphabet raw block target slot failure)
          innerEq
        have slotEq : slot = position := range_getElem?_eq valid.source_at
        subst slotEq
        exact valid
  · intro valid
    unfold edgeFailure?
    have innerEq : firstFailure? (List.range block.term.arity)
        (fun _ slot => slotFailure? alphabet raw block target slot) =
          some (edge.1, edge.1, edge.2) :=
      (firstFailure?_eq_some_iff
        (fun _ slot failure => slotFailure?_eq_some_iff alphabet raw block target slot failure)).mpr
        valid
    simp [innerEq]

private theorem edgeFailure?_eq_none_iff [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (block : RawBlock Ty) (index : Nat) (target : BlockId) :
    edgeFailure? alphabet raw block index target = none ↔
      ∀ slot, slot ∈ List.range block.term.arity → SlotWF alphabet raw block target slot := by
  unfold edgeFailure?
  cases innerEq : firstFailure? (List.range block.term.arity)
      (fun _ slot => slotFailure? alphabet raw block target slot) with
  | some result =>
      rcases result with ⟨position, slot, payload⟩
      simp only [reduceCtorEq, false_iff]
      intro wf
      have valid := firstFailure?_eq_some_valid
        (fun _ slot failure => slotFailure?_eq_some_iff alphabet raw block target slot failure)
        innerEq
      have slotWF := wf slot (List.mem_iff_getElem?.mpr ⟨position, valid.source_at⟩)
      have clear := (slotFailure?_eq_none_iff alphabet raw block target slot).mpr slotWF
      have failed := (slotFailure?_eq_some_iff alphabet raw block target slot payload).mpr
        valid.fails_at
      rw [clear] at failed
      contradiction
  | none =>
      simp only [true_iff]
      intro slot slotMem
      obtain ⟨position, slotAt⟩ := List.mem_iff_getElem?.mp slotMem
      have clear := firstFailure?_eq_none_iff.mp innerEq position slot slotAt
      exact (slotFailure?_eq_none_iff alphabet raw block target slot).mp clear

private def argumentBlockFailure? [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (_ : Nat) (block : RawBlock Ty) :
    Option (Nat × BlockId × (Nat × DiagnosticPayload Ty)) :=
  firstFailure? block.term.successors (edgeFailure? alphabet raw block)

private theorem argumentBlockFailure?_eq_some_iff [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (index : Nat) (block : RawBlock Ty)
    (witness : Nat × BlockId × (Nat × DiagnosticPayload Ty)) :
    argumentBlockFailure? alphabet raw index block = some witness ↔
      FirstFailureAt block.term.successors
        (fun _ successor edge =>
          FirstFailureAt (List.range block.term.arity)
            (fun _ slot failure =>
              ArgumentFailureValid alphabet raw block successor slot failure)
            edge.1 edge.1 edge.2)
        witness.1 witness.2.1 witness.2.2 := by
  rcases witness with ⟨successorIndex, target, edge⟩
  exact firstFailure?_eq_some_iff (edgeFailure?_eq_some_iff alphabet raw block)

private theorem argumentBlockFailure?_eq_none_iff [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (index : Nat) (block : RawBlock Ty) :
    argumentBlockFailure? alphabet raw index block = none ↔
      ArgumentsWF alphabet raw block := by
  unfold argumentBlockFailure?
  rw [firstFailure?_eq_none_iff]
  constructor
  · intro clear target targetMem
    obtain ⟨successorIndex, targetAt⟩ := List.mem_iff_getElem?.mp targetMem
    exact (edgeFailure?_eq_none_iff alphabet raw block successorIndex target).mp
      (clear successorIndex target targetAt)
  · intro wf successorIndex target targetAt
    exact (edgeFailure?_eq_none_iff alphabet raw block successorIndex target).mpr
      (wf target (List.mem_iff_getElem?.mpr ⟨successorIndex, targetAt⟩))

/-! ## The cycle clause (`unchosenCycle`) -/

private def cycleFailure? (raw : RawFlow Ty) (_ : Nat) (block : RawBlock Ty) : Option BlockId :=
  if (raw.noChooseSuccessors block.id).any (fun next => decide (block.id ∈ raw.reachSet next)) then
    some block.id
  else none

private theorem cycleFailure?_eq_some_iff (raw : RawFlow Ty) (index : Nat)
    (block : RawBlock Ty) (reported : BlockId) :
    cycleFailure? raw index block = some reported ↔
      reported = block.id ∧
        ∃ next : BlockId,
          EdgeNoChoose raw block.id next ∧ ReachableNoChoose raw next block.id := by
  unfold cycleFailure?
  by_cases closes : (raw.noChooseSuccessors block.id).any
      (fun next => decide (block.id ∈ raw.reachSet next)) = true
  · rw [if_pos closes]
    simp only [Option.some.injEq]
    constructor
    · intro reportedEq
      obtain ⟨next, nextMem, reaches⟩ := List.any_eq_true.mp closes
      exact ⟨reportedEq.symm, next, RawFlow.mem_noChooseSuccessors.mp nextMem,
        RawFlow.mem_reachSet.mp (of_decide_eq_true reaches)⟩
    · rintro ⟨reportedEq, _⟩
      exact reportedEq.symm
  · rw [if_neg closes]
    simp only [reduceCtorEq, false_iff, not_and]
    rintro _ ⟨next, edge, reach⟩
    apply closes
    exact List.any_eq_true.mpr
      ⟨next, RawFlow.mem_noChooseSuccessors.mpr edge, decide_eq_true (RawFlow.mem_reachSet.mpr reach)⟩

private theorem cycles_of_scan_clear (raw : RawFlow Ty)
    (clear : firstFailure? raw.blocks (cycleFailure? raw) = none) : CyclesWF raw := by
  intro source target edge reach
  obtain ⟨block, blockMem, idEq, notChoose, targetMem⟩ := edge
  obtain ⟨index, blockAt⟩ := List.mem_iff_getElem?.mp blockMem
  have checked := firstFailure?_eq_none_iff.mp clear index block blockAt
  have failed : cycleFailure? raw index block = some block.id :=
    (cycleFailure?_eq_some_iff raw index block block.id).mpr
      ⟨rfl, target, ⟨block, blockMem, rfl, notChoose, targetMem⟩, idEq ▸ reach⟩
  rw [checked] at failed
  contradiction

/-! ## Decidability of every clause -/

private def clauseHoldsDecidable [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) : Decidable (ClauseHolds alphabet raw clause) := by
  cases clause with
  | alphabetMismatch | duplicateBlockId | duplicateDecisionId |
    nonCanonicalBlockOrder | emptyRoots | duplicateRoot |
    nonCanonicalRootOrder | entryNotRoot | danglingRoot |
    danglingSuccessor =>
      unfold ClauseHolds AlphabetWF ReferencesWF
      infer_instance
  | unknownOperation =>
      show Decidable (OperationsWF alphabet raw)
      unfold OperationsWF
      letI : DecidablePred (OperationWF alphabet) :=
        fun block => decidable_of_iff _ (unknownOperationFailure?_eq_none_iff alphabet 0 block)
      infer_instance
  | entryTypeMismatch =>
      exact localEntryWFDecidable raw
  | termTypeMismatch =>
      show Decidable (∀ block, block ∈ raw.blocks → OperandsWF alphabet raw block)
      letI : DecidablePred (OperandsWF alphabet raw) :=
        fun block => decidable_of_iff _ (operandFailure?_eq_none_iff alphabet raw block)
      infer_instance
  | unknownVariable =>
      show Decidable (∀ block, block ∈ raw.blocks → block.VarsWF)
      letI : DecidablePred (RawBlock.VarsWF (Ty := Ty)) :=
        fun block => decidable_of_iff _ (variableBlockFailure?_eq_none_iff 0 block)
      infer_instance
  | argumentArity =>
      show Decidable (∀ block, block ∈ raw.blocks → ArityWF raw block)
      letI : DecidablePred (ArityWF raw) :=
        fun block => decidable_of_iff _ (arityBlockFailure?_eq_none_iff raw 0 block)
      infer_instance
  | argumentTypeMismatch =>
      show Decidable (∀ block, block ∈ raw.blocks → ArgumentsWF alphabet raw block)
      letI : DecidablePred (ArgumentsWF alphabet raw) :=
        fun block => decidable_of_iff _ (argumentBlockFailure?_eq_none_iff alphabet raw 0 block)
      infer_instance
  | unchosenCycle =>
      exact decidable_of_iff _ cyclesChoose_iff

private structure PreciseFailure (alphabet : FlowAlphabet Ty)
    (raw : RawFlow Ty) (clause : AdmissionClause) where
  site : CheckSite
  payload : DiagnosticPayload Ty
  valid : Diagnostic.Valid alphabet raw ⟨clause, site, payload⟩

private def preciseFailure [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause)
    (refute : ¬ ClauseHolds alphabet raw clause) :
    PreciseFailure alphabet raw clause := by
  cases clause with
  | alphabetMismatch =>
      refine ⟨.flow, .alphabet alphabet.id raw.alphabet,
        .alphabetMismatch ?_⟩
      exact refute
  | duplicateBlockId =>
      cases found : firstFailure? raw.blocks (duplicateBlockFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have noDuplicates : (raw.blocks.map RawBlock.id).Nodup := by
            apply map_nodup_of_no_prefix_duplicate raw.blocks RawBlock.id
            intro index block blockAt
            have checked := clear index block blockAt
            intro duplicate
            have mappedDuplicate :
                block.id ∈ (raw.blocks.map RawBlock.id).take index := by
              simpa using duplicate
            simp [duplicateBlockFailure?, mappedDuplicate] at checked
          exact (refute noDuplicates).elim
      | some result =>
          rcases result with ⟨index, block, reported⟩
          have first := firstFailure?_eq_some_valid
            (duplicateBlockFailure?_eq_some_iff raw) found
          have reportedEq : reported = block.id := first.fails_at.1
          subst reported
          exact ⟨.block index, .block block.id, .duplicateBlockId first⟩
  | duplicateDecisionId =>
      cases found : firstFailure? raw.blocks (duplicateDecisionFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have noDuplicates : (localDecisionIds raw).Nodup := by
            unfold localDecisionIds
            apply filterMap_nodup_of_no_prefix_duplicate
            intro index block blockAt decision selected duplicate
            have checked := clear index block blockAt
            cases termEq : block.term with
            | ret | jump | perform => simp [RawTerm.decision?, termEq] at selected
            | choose actual left right args =>
                simp [RawTerm.decision?, termEq] at selected
                subst decision
                simp [duplicateDecisionFailure?, termEq, duplicate] at checked
          exact (refute noDuplicates).elim
      | some result =>
          rcases result with ⟨index, block, decision⟩
          have first := firstFailure?_eq_some_valid
            (duplicateDecisionFailure?_eq_some_iff raw) found
          exact ⟨.decision block.id, .decision decision,
            .duplicateDecisionId first⟩
  | nonCanonicalBlockOrder =>
      cases found : firstFailure? raw.blocks
          (orderFailure? raw.blocks
            (fun block : RawBlock Ty => block.id.value)) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have ordered : raw.blocks.Pairwise
              (fun left right => left.id.value < right.id.value) := by
            apply pairwise_nat_of_adjacent raw.blocks
              (fun block : RawBlock Ty => block.id.value)
            intro index block previous positive blockAt previousAt
            have checked := clear index block blockAt
            by_cases ordered : previous.id.value < block.id.value
            · exact ordered
            · have failed := (orderFailure?_eq_some_iff raw.blocks
                (fun candidate : RawBlock Ty => candidate.id.value)
                index block block).mpr
                  ⟨rfl, positive, ⟨previous, previousAt, ordered⟩⟩
              rw [checked] at failed
              contradiction
          exact (refute ordered).elim
      | some result =>
          rcases result with ⟨index, block, reported⟩
          have first := firstFailure?_eq_some_valid
            (orderFailure?_eq_some_iff raw.blocks
              (fun candidate : RawBlock Ty => candidate.id.value)) found
          have reportedEq : reported = block := first.fails_at.1
          subst reported
          have converted : FirstFailureAt raw.blocks
              (fun candidateIndex candidate (reported : BlockId) =>
                reported = candidate.id ∧
                0 < candidateIndex ∧
                ∃ previous,
                  raw.blocks[candidateIndex - 1]? = some previous ∧
                  ¬ previous.id.value < candidate.id.value)
              index block block.id := by
            refine ⟨first.source_at, ?_, ?_⟩
            · exact ⟨rfl, first.fails_at.2⟩
            · intro priorIndex priorBlock priorLt priorAt priorFailure failed
              exact first.prior_clear priorIndex priorBlock priorLt priorAt
                priorBlock ⟨rfl, failed.2⟩
          exact ⟨.block index, .block block.id,
            .nonCanonicalBlockOrder converted⟩
  | emptyRoots =>
      by_cases empty : raw.roots = []
      · exact ⟨.flow, .none, .emptyRoots empty⟩
      · exact (refute empty).elim
  | duplicateRoot =>
      cases found : firstFailure? raw.roots (duplicateRootFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have noDuplicates : raw.roots.Nodup := by
            apply nodup_of_no_prefix_duplicate raw.roots
            intro index root rootAt duplicate
            have checked := clear index root rootAt
            simp [duplicateRootFailure?, duplicate] at checked
          exact (refute noDuplicates).elim
      | some result =>
          rcases result with ⟨index, root, reported⟩
          have first := firstFailure?_eq_some_valid
            (duplicateRootFailure?_eq_some_iff raw) found
          have reportedEq : reported = root := first.fails_at.1
          subst reported
          exact ⟨.root index, .block root, .duplicateRoot first⟩
  | nonCanonicalRootOrder =>
      cases found : firstFailure? raw.roots
          (orderFailure? raw.roots BlockId.value) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have ordered : raw.roots.Pairwise
              (fun left right => left.value < right.value) := by
            apply pairwise_nat_of_adjacent raw.roots BlockId.value
            intro index root previous positive rootAt previousAt
            have checked := clear index root rootAt
            by_cases ordered : previous.value < root.value
            · exact ordered
            · have failed := (orderFailure?_eq_some_iff raw.roots
                BlockId.value index root root).mpr
                  ⟨rfl, positive, ⟨previous, previousAt, ordered⟩⟩
              rw [checked] at failed
              contradiction
          exact (refute ordered).elim
      | some result =>
          rcases result with ⟨index, root, reported⟩
          have first := firstFailure?_eq_some_valid
            (orderFailure?_eq_some_iff raw.roots BlockId.value) found
          have reportedEq : reported = root := first.fails_at.1
          subst reported
          exact ⟨.root index, .block root,
            .nonCanonicalRootOrder first⟩
  | entryNotRoot =>
      exact ⟨.entry, .block raw.entry, .entryNotRoot refute⟩
  | danglingRoot =>
      cases found : firstFailure? raw.roots (danglingRootFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allResolve : ∀ root, root ∈ raw.roots →
              (lookupBlock raw root).isSome = true := by
            intro root rootMem
            obtain ⟨index, rootAt⟩ := List.mem_iff_getElem?.mp rootMem
            have checked := clear index root rootAt
            cases lookupEq : lookupBlock raw root with
            | none => simp [danglingRootFailure?, lookupEq] at checked
            | some block => rfl
          exact (refute allResolve).elim
      | some result =>
          rcases result with ⟨index, root, reported⟩
          have first := firstFailure?_eq_some_valid
            (danglingRootFailure?_eq_some_iff raw) found
          have reportedEq : reported = root := first.fails_at.1
          subst reported
          exact ⟨.root index, .block root, .danglingRoot first⟩
  | danglingSuccessor =>
      cases found : firstFailure? raw.blocks (danglingBlockFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allResolve : ReferencesWF raw := by
            intro block blockMem target targetMem
            obtain ⟨blockIndex, blockAt⟩ :=
              List.mem_iff_getElem?.mp blockMem
            have blockClear := clear blockIndex block blockAt
            unfold danglingBlockFailure? at blockClear
            cases innerEq : firstPreciseDanglingSuccessorIn? raw block with
            | some result => simp [innerEq] at blockClear
            | none =>
                have innerClear := firstFailure?_eq_none_iff.mp innerEq
                obtain ⟨targetIndex, targetAt⟩ :=
                  List.mem_iff_getElem?.mp targetMem
                have targetClear := innerClear targetIndex target targetAt
                cases lookupEq : lookupBlock raw target with
                | none =>
                    simp [danglingSuccessorFailure?, lookupEq] at targetClear
                | some targetBlock => rfl
          exact (refute allResolve).elim
      | some result =>
          rcases result with ⟨blockIndex, block, witness⟩
          have first := firstFailure?_eq_some_valid
            (danglingBlockFailure?_eq_some_iff raw) found
          exact ⟨.successor block.id witness.1, .block witness.2,
            .danglingSuccessor first⟩
  | unknownOperation =>
      cases found : firstFailure? raw.blocks
          (unknownOperationFailure? alphabet) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allKnown : OperationsWF alphabet raw := by
            intro block blockMem
            obtain ⟨index, blockAt⟩ := List.mem_iff_getElem?.mp blockMem
            exact (unknownOperationFailure?_eq_none_iff alphabet index block).mp
              (clear index block blockAt)
          exact (refute allKnown).elim
      | some result =>
          rcases result with ⟨index, block, operation⟩
          have first := firstFailure?_eq_some_valid
            (unknownOperationFailure?_eq_some_iff alphabet) found
          exact ⟨.operation block.id, .operation operation,
            .unknownOperation first⟩
  | entryTypeMismatch =>
      cases entryEq : lookupBlock raw raw.entry with
      | none =>
          exact ⟨.entry, .block raw.entry, .entryMissing entryEq⟩
      | some block =>
          cases paramsEq : block.params with
          | nil =>
              refine ⟨.entry, .arity 1 block.params.length, .entryArity entryEq ?_⟩
              rw [paramsEq]
              exact Nat.zero_ne_one
          | cons actual rest =>
              cases rest with
              | nil =>
                  have mismatch : actual ≠ raw.inputTy := by
                    intro typed
                    apply refute
                    simp [ClauseHolds, EntryWF, entryEq, paramsEq, typed]
                  exact ⟨.entry, .typeMismatch raw.inputTy actual,
                    .entryTypeMismatch entryEq paramsEq mismatch⟩
              | cons second more =>
                  refine ⟨.entry, .arity 1 block.params.length, .entryArity entryEq ?_⟩
                  rw [paramsEq]
                  simp only [List.length_cons]
                  omega
  | termTypeMismatch =>
      cases found : firstFailure? raw.blocks
          (fun _ block => operandFailure? alphabet raw block) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allTyped : ∀ block, block ∈ raw.blocks →
              OperandsWF alphabet raw block := by
            intro block blockMem
            obtain ⟨index, blockAt⟩ := List.mem_iff_getElem?.mp blockMem
            exact (operandFailure?_eq_none_iff alphabet raw block).mp
              (clear index block blockAt)
          exact (refute allTyped).elim
      | some result =>
          rcases result with ⟨index, block, payload⟩
          have first := firstFailure?_eq_some_valid
            (fun _ candidate failure =>
              operandFailure?_eq_some_iff alphabet raw candidate failure) found
          exact ⟨.term block.id, payload, .termTypeMismatch first⟩
  | unknownVariable =>
      cases found : firstFailure? raw.blocks variableBlockFailure? with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allInRange : ∀ block, block ∈ raw.blocks → block.VarsWF := by
            intro block blockMem
            obtain ⟨index, blockAt⟩ := List.mem_iff_getElem?.mp blockMem
            exact (variableBlockFailure?_eq_none_iff index block).mp
              (clear index block blockAt)
          exact (refute allInRange).elim
      | some result =>
          rcases result with ⟨blockIndex, block, witness⟩
          have first := firstFailure?_eq_some_valid
            variableBlockFailure?_eq_some_iff found
          exact ⟨.term block.id, .variable witness.2, .unknownVariable first⟩
  | argumentArity =>
      cases found : firstFailure? raw.blocks (arityBlockFailure? raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allSized : ∀ block, block ∈ raw.blocks → ArityWF raw block := by
            intro block blockMem
            obtain ⟨index, blockAt⟩ := List.mem_iff_getElem?.mp blockMem
            exact (arityBlockFailure?_eq_none_iff raw index block).mp
              (clear index block blockAt)
          exact (refute allSized).elim
      | some result =>
          rcases result with ⟨blockIndex, block, witness⟩
          have first := firstFailure?_eq_some_valid
            (arityBlockFailure?_eq_some_iff raw) found
          exact ⟨.successor block.id witness.1, .arity block.term.arity witness.2.2,
            .argumentArity first⟩
  | argumentTypeMismatch =>
      cases found : firstFailure? raw.blocks (argumentBlockFailure? alphabet raw) with
      | none =>
          have clear := firstFailure?_eq_none_iff.mp found
          have allTyped : ∀ block, block ∈ raw.blocks → ArgumentsWF alphabet raw block := by
            intro block blockMem
            obtain ⟨index, blockAt⟩ := List.mem_iff_getElem?.mp blockMem
            exact (argumentBlockFailure?_eq_none_iff alphabet raw index block).mp
              (clear index block blockAt)
          exact (refute allTyped).elim
      | some result =>
          rcases result with ⟨blockIndex, block, witness⟩
          have first := firstFailure?_eq_some_valid
            (argumentBlockFailure?_eq_some_iff alphabet raw) found
          exact ⟨.argument block.id witness.1 witness.2.2.1, witness.2.2.2,
            .argumentTypeMismatch first⟩
  | unchosenCycle =>
      cases found : firstFailure? raw.blocks (cycleFailure? raw) with
      | none => exact (refute (cycles_of_scan_clear raw found)).elim
      | some result =>
          rcases result with ⟨index, block, reported⟩
          have first := firstFailure?_eq_some_valid
            (cycleFailure?_eq_some_iff raw) found
          have reportedEq : reported = block.id := first.fails_at.1
          subst reported
          exact ⟨.block index, .block block.id, .unchosenCycle first⟩

/-- A clause-indexed result makes an unrelated diagnostic unrepresentable. -/
private inductive ClauseResult (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) (holds : Prop) where
  | pass (proof : holds)
  | fail (site : CheckSite) (payload : DiagnosticPayload Ty)
      (valid : Diagnostic.Valid alphabet raw ⟨clause, site, payload⟩)
      (refute : ¬ holds)

private def ClauseResult.diagnostic?
    {Ty : Type uTy} {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {clause : AdmissionClause} {holds : Prop} :
    ClauseResult alphabet raw clause holds → Option (Diagnostic Ty)
  | .pass _ => none
  | .fail site payload _ _ => some ⟨clause, site, payload⟩

private def checkClause [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) :
    ClauseResult alphabet raw clause (ClauseHolds alphabet raw clause) :=
  letI := clauseHoldsDecidable alphabet raw clause
  if holds : ClauseHolds alphabet raw clause then
    .pass holds
  else
    let failure := preciseFailure alphabet raw clause holds
    .fail failure.site failure.payload failure.valid holds

/-- Diagnose exactly one clause, independently of the global scan order. -/
def diagnoseAt [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (clause : AdmissionClause) : Option (Diagnostic Ty) :=
  (checkClause alphabet raw clause).diagnostic?

/-- Every reported clause-local diagnostic carries its exact source witness. -/
theorem diagnoseAt_some_valid [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {clause : AdmissionClause} {diagnostic : Diagnostic Ty}
    (found : diagnoseAt alphabet raw clause = some diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic := by
  unfold diagnoseAt at found
  generalize resultEq : checkClause alphabet raw clause = result at found
  cases result with
  | pass proof => simp [ClauseResult.diagnostic?] at found
  | fail site payload valid refute =>
      simp [ClauseResult.diagnostic?] at found
      cases found
      exact valid

private theorem diagnoseAt_eq_none_iff [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {clause : AdmissionClause} :
    diagnoseAt alphabet raw clause = none ↔
      ClauseHolds alphabet raw clause := by
  unfold diagnoseAt
  generalize resultEq : checkClause alphabet raw clause = result
  cases result with
  | pass proof => simp [ClauseResult.diagnostic?, proof]
  | fail site payload valid refute => simp [ClauseResult.diagnostic?, refute]

private theorem diagnoseAt_clause [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {clause : AdmissionClause} {diagnostic : Diagnostic Ty}
    (found : diagnoseAt alphabet raw clause = some diagnostic) :
    diagnostic.clause = clause := by
  unfold diagnoseAt at found
  generalize resultEq : checkClause alphabet raw clause = result at found
  cases result with
  | pass proof => simp [ClauseResult.diagnostic?] at found
  | fail site payload valid refute =>
      simp [ClauseResult.diagnostic?] at found
      cases found
      rfl

private theorem flowWF_iff_clauses [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    FlowWF alphabet raw ↔
      ∀ clause, clause ∈ scan → ClauseHolds alphabet raw clause := by
  constructor
  · intro wf clause _
    rcases idsWF_view raw |>.mp wf.ids with ⟨blockIds, blockOrder, decisions⟩
    rcases wf.roots with
      ⟨rootsNonempty, rootIds, rootOrder, entryRoot, rootsResolve⟩
    rcases wf.terms with ⟨vars, arity, arguments, operands⟩
    cases clause with
    | alphabetMismatch => exact wf.alphabet
    | duplicateBlockId => exact blockIds
    | duplicateDecisionId => exact decisions
    | nonCanonicalBlockOrder => exact blockOrder
    | emptyRoots => exact rootsNonempty
    | duplicateRoot => exact rootIds
    | nonCanonicalRootOrder => exact rootOrder
    | entryNotRoot => exact entryRoot
    | danglingRoot => exact rootsResolve
    | danglingSuccessor => exact wf.references
    | unknownOperation => exact wf.operations
    | entryTypeMismatch => exact wf.entry
    | termTypeMismatch => exact operands
    | unknownVariable => exact vars
    | argumentArity => exact arity
    | argumentTypeMismatch => exact arguments
    | unchosenCycle => exact wf.cycles
  · intro clauses
    have holds (clause : AdmissionClause) : ClauseHolds alphabet raw clause :=
      clauses clause (by cases clause <;> simp [scan])
    exact {
      alphabet := holds .alphabetMismatch
      ids := idsWF_view raw |>.mpr ⟨
        holds .duplicateBlockId,
        holds .nonCanonicalBlockOrder,
        holds .duplicateDecisionId⟩
      roots := ⟨
        holds .emptyRoots,
        holds .duplicateRoot,
        holds .nonCanonicalRootOrder,
        holds .entryNotRoot,
        holds .danglingRoot⟩
      references := holds .danglingSuccessor
      operations := holds .unknownOperation
      entry := holds .entryTypeMismatch
      terms := ⟨holds .unknownVariable, holds .argumentArity,
        holds .argumentTypeMismatch, holds .termTypeMismatch⟩
      cycles := holds .unchosenCycle
    }

/-- A diagnostic is first exactly when its clause fails and every prior clause passes. -/
structure FirstDiagnostic [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (diagnostic : Diagnostic Ty) : Prop where
  condemns : diagnoseAt alphabet raw diagnostic.clause = some diagnostic
  prior : ∀ clause,
    clause ∈ scan.takeWhile
      (fun candidate => decide (candidate != diagnostic.clause)) →
    diagnoseAt alphabet raw clause = none

namespace FirstDiagnostic

/-- A globally first diagnostic retains the exact witness from its clause. -/
theorem valid [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {diagnostic : Diagnostic Ty}
    (first : FirstDiagnostic alphabet raw diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic :=
  diagnoseAt_some_valid first.condemns

end FirstDiagnostic

namespace Diagnostic

/-- All seventeen independent checks pass exactly when the eight WF fields hold. -/
theorem clause_all_complete [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty} :
    FlowWF alphabet raw ↔
      ∀ clause, clause ∈ scan → diagnoseAt alphabet raw clause = none := by
  constructor
  · intro wf clause member
    exact diagnoseAt_eq_none_iff.mpr
      ((flowWF_iff_clauses alphabet raw).mp wf clause member)
  · intro clear
    apply (flowWF_iff_clauses alphabet raw).mpr
    intro clause member
    exact diagnoseAt_eq_none_iff.mp (clear clause member)

end Diagnostic

private theorem scan_nodup : scan.Nodup := by decide

/-- The clauses scanned before `clause`, in order. -/
private def clausesBefore (clause : AdmissionClause) : List AdmissionClause :=
  scan.takeWhile fun candidate => decide (candidate != clause)

private def clausesAfter (clause : AdmissionClause) : List AdmissionClause :=
  scan.drop ((clausesBefore clause).length + 1)

private theorem clause_split (clause : AdmissionClause) :
    scan = clausesBefore clause ++ clause :: clausesAfter clause := by
  cases clause <;> rfl

private theorem takeWhile_before
    (clause : AdmissionClause) {before after : List AdmissionClause}
    (split : scan = before ++ clause :: after) :
    scan.takeWhile (fun candidate => decide (candidate != clause)) = before := by
  have noDuplicates : (before ++ clause :: after).Nodup :=
    split ▸ scan_nodup
  have clauseNotInBefore : clause ∉ before := by
    rw [List.nodup_append] at noDuplicates
    intro clauseInBefore
    exact (noDuplicates.2.2 clause clauseInBefore clause (by simp)) rfl
  rw [split, List.takeWhile_append_of_pos]
  · simp
  · intro candidate candidateInBefore
    simp only [decide_eq_true_eq]
    apply bne_iff_ne.mpr
    intro candidateEqClause
    subst candidate
    exact clauseNotInBefore candidateInBefore

private def firstDiagnostic? [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    Option (Diagnostic Ty) :=
  scan.findSome? (diagnoseAt alphabet raw)

private theorem firstDiagnostic?_eq_none_iff [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty} :
    firstDiagnostic? alphabet raw = none ↔
      ∀ clause, clause ∈ scan → diagnoseAt alphabet raw clause = none := by
  simp [firstDiagnostic?]

private theorem firstDiagnostic?_eq_some_iff [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {diagnostic : Diagnostic Ty} :
    firstDiagnostic? alphabet raw = some diagnostic ↔
      FirstDiagnostic alphabet raw diagnostic := by
  unfold firstDiagnostic?
  constructor
  · intro found
    obtain ⟨before, clause, after, split, condemns, prior⟩ :=
      List.findSome?_eq_some_iff.mp found
    have clauseEq : diagnostic.clause = clause :=
      diagnoseAt_clause condemns
    subst clause
    refine ⟨condemns, ?_⟩
    intro candidate candidateInPrior
    rw [takeWhile_before diagnostic.clause split] at candidateInPrior
    exact prior candidate candidateInPrior
  · intro first
    let before := clausesBefore diagnostic.clause
    let after := clausesAfter diagnostic.clause
    have split : scan = before ++ diagnostic.clause :: after :=
      clause_split diagnostic.clause
    apply List.findSome?_eq_some_iff.mpr
    refine ⟨before, diagnostic.clause, after, split, first.condemns, ?_⟩
    intro candidate candidateInBefore
    apply first.prior candidate
    rw [takeWhile_before diagnostic.clause split]
    exact candidateInBefore

/-- The proof-carrying result of successful admission. -/
structure CheckedFlow.{uTy, uOp} {Ty : Type uTy}
    (alphabet : FlowAlphabet.{uTy, uOp} Ty) : Type uTy where
  private mk ::
  raw : RawFlow Ty
  wf : FlowWF alphabet raw

namespace CheckedFlow

/-- Forget the proof while retaining the complete first-order document. -/
def erase {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
    (checked : CheckedFlow alphabet) : RawFlow Ty :=
  checked.raw

@[simp] theorem erase_eq_raw
    {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
    (checked : CheckedFlow alphabet) :
    checked.erase = checked.raw := rfl

@[ext] theorem ext
    {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
    {left right : CheckedFlow alphabet}
    (raw : left.raw = right.raw) : left = right := by
  cases left
  cases right
  cases raw
  rfl

end CheckedFlow

/-- Check every clause in the fixed order and seal the raw graph on success. -/
def admit [DecidableEq Ty]
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    Except (Diagnostic Ty) (CheckedFlow alphabet) :=
  match found : firstDiagnostic? alphabet raw with
  | none =>
      .ok <| CheckedFlow.mk raw <|
        Diagnostic.clause_all_complete.mpr <|
          firstDiagnostic?_eq_none_iff.mp found
  | some diagnostic => .error diagnostic

/-- Successful admission proves all seven WF fields for the original raw graph. -/
theorem admit_sound [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {checked : CheckedFlow alphabet}
    (accepted : admit alphabet raw = .ok checked) :
    FlowWF alphabet raw := by
  unfold admit at accepted
  split at accepted
  · rename_i found
    exact Diagnostic.clause_all_complete.mpr
      (firstDiagnostic?_eq_none_iff.mp found)
  · contradiction

/-- Every graph satisfying the frozen seven clauses is admitted. -/
theorem admit_complete [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) :
    ∃ checked : CheckedFlow alphabet, admit alphabet raw = .ok checked := by
  have clear := Diagnostic.clause_all_complete.mp wf
  have found : firstDiagnostic? alphabet raw = none :=
    firstDiagnostic?_eq_none_iff.mpr clear
  refine ⟨CheckedFlow.mk raw wf, ?_⟩
  unfold admit
  split
  · congr 2
  · rename_i diagnostic impossible
    rw [found] at impossible
    contradiction

/-- Admission reports some error exactly when the raw graph is not well formed. -/
theorem error_iff_not_wf [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty} :
    (∃ diagnostic : Diagnostic Ty,
      admit alphabet raw = .error diagnostic) ↔
    ¬ FlowWF alphabet raw := by
  constructor
  · rintro ⟨diagnostic, errored⟩ wf
    obtain ⟨checked, accepted⟩ := admit_complete wf
    rw [errored] at accepted
    contradiction
  · intro notWf
    cases resultEq : admit alphabet raw with
    | error diagnostic => exact ⟨diagnostic, rfl⟩
    | ok checked => exact (notWf (admit_sound resultEq)).elim

/-- A particular error is returned exactly when it is the first failing clause. -/
theorem error_iff_firstDiagnostic [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {diagnostic : Diagnostic Ty} :
    admit alphabet raw = .error diagnostic ↔
      FirstDiagnostic alphabet raw diagnostic := by
  rw [← firstDiagnostic?_eq_some_iff]
  unfold admit
  split
  · rename_i clear
    constructor
    · intro impossible
      contradiction
    · intro found
      rw [clear] at found
      contradiction
  · rename_i notClear
    simp [notClear]

/-- Every observable admission error carries its exact first source witness. -/
theorem admit_error_valid [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {diagnostic : Diagnostic Ty}
    (errored : admit alphabet raw = .error diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic :=
  (error_iff_firstDiagnostic.mp errored).valid

/-- Erasing any checked flow retains its WF evidence. -/
theorem erase_wf (checked : CheckedFlow alphabet) :
    FlowWF alphabet checked.erase :=
  by simpa using checked.wf

/-- A successful admission result erases to the exact input raw graph. -/
theorem erase_admit [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {checked : CheckedFlow alphabet}
    (accepted : admit alphabet raw = .ok checked) :
    checked.erase = raw := by
  unfold admit at accepted
  split at accepted
  · cases accepted
    simp
  · contradiction

/-- Re-admitting a checked erasure returns the same proof-carrying value. -/
theorem admit_erase [DecidableEq Ty]
    {alphabet : FlowAlphabet Ty} (checked : CheckedFlow alphabet) :
    admit alphabet checked.erase = .ok checked := by
  have clear := Diagnostic.clause_all_complete.mp checked.wf
  have found : firstDiagnostic? alphabet checked.erase = none :=
    firstDiagnostic?_eq_none_iff.mpr (by simpa using clear)
  unfold admit
  split
  · congr 2
  · rename_i diagnostic impossible
    rw [found] at impossible
    contradiction

end Effects
