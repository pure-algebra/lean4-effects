/-
Contract packet: `test/contracts/flow-v2.contract.md`

Breaker-owned red battery for Flow v2 (Effects v0.4.0). The implementation
phase must not edit this file. It is red until the parameterised carrier
(`Var`, block parameters, four-ary terms), the cycle clause (`CyclesWF`,
`cyclesChoose`, `cyclesChoose_iff`), and the four new admission clauses exist.

Every receipt here is kernel-checked: `#check` ascriptions, `rfl`, `decide`,
and hand proofs. While the carrier is v0.3.1 a v2-shaped literal elaborates
only as an argument of a frozen v2 name, so the red log consists of unknown
identifier / unknown constant diagnostics for the frozen names and nothing
else. `autoImplicit` is off because a missing `Var` would otherwise be
auto-bound as a type variable. The executable admission receipts (`#guard`
over `admit`) live in `EffectsTest/Counterexamples/Flow/FlowV2.lean`.
-/

import Effects.Flow.Admission
import Effects.Flow.Block
import Effects.Flow.Checked
import Effects.Flow.Raw

set_option autoImplicit false

namespace EffectsTest.Flow.FlowV2Contract

open Effects

universe uTy uOp uA uB

section SurfaceSnapshot

/-! D0: nominal identifiers (retained) and block-parameter positions. -/

#check (@BlockId : Type)
#check (@BlockId.mk : Nat → BlockId)
#check (@BlockId.value : BlockId → Nat)
#synth DecidableEq BlockId

#check (@OperationId : Type)
#check (@OperationId.mk : Nat → OperationId)
#check (@OperationId.value : OperationId → Nat)
#synth DecidableEq OperationId

#check (@AlphabetId : Type)
#check (@AlphabetId.mk : Nat → AlphabetId)
#check (@AlphabetId.value : AlphabetId → Nat)
#synth DecidableEq AlphabetId

#check (@DecisionId : Type)
#check (@DecisionId.mk : Nat → DecisionId)
#check (@DecisionId.value : DecisionId → Nat)
#synth DecidableEq DecisionId

#check (@Var : Type)
#check (@Var.mk : Nat → Var)
#check (@Var.index : Var → Nat)
#synth DecidableEq Var
#synth Repr Var

/-! D1: one closed operation alphabet (retained). -/

#check (@FlowAlphabet.id :
  ∀ {Ty : Type uTy}, FlowAlphabet.{uTy, uOp} Ty → AlphabetId)

#check (@FlowAlphabet.Op :
  ∀ {Ty : Type uTy}, FlowAlphabet.{uTy, uOp} Ty → Type uOp)

#check (@FlowAlphabet.operationId :
  ∀ {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty),
    alphabet.Op → OperationId)

#check (@FlowAlphabet.lookup :
  ∀ {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty),
    OperationId → Option alphabet.Op)

#check (@FlowAlphabet.requestTy :
  ∀ {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty),
    alphabet.Op → Ty)

#check (@FlowAlphabet.answerTy :
  ∀ {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty),
    alphabet.Op → Ty)

#check (@FlowAlphabet.lookup_operationId :
  ∀ {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty)
      (operation : alphabet.Op),
    alphabet.lookup (alphabet.operationId operation) = some operation)

#check (@FlowAlphabet.operationId_of_lookup :
  ∀ {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty)
      {id : OperationId} {operation : alphabet.Op},
    alphabet.lookup id = some operation → alphabet.operationId operation = id)

/-! D2: terms over block parameters, blocks with parameter lists, documents. -/

#check (@RawTerm.ret : Var → RawTerm)
#check (@RawTerm.jump : BlockId → List Var → RawTerm)
#check (@RawTerm.perform : OperationId → Var → BlockId → List Var → RawTerm)
#check (@RawTerm.choose : DecisionId → BlockId → BlockId → List Var → RawTerm)
#check (@RawTerm.successors : RawTerm → List BlockId)
#check (@RawTerm.args : RawTerm → List Var)
#check (@RawTerm.operands : RawTerm → List Var)
#check (@RawTerm.arity : RawTerm → Nat)
#check (@RawTerm.isChoose : RawTerm → Bool)
#check (@RawTerm.decision? : RawTerm → Option DecisionId)
#synth DecidableEq RawTerm
#synth Repr RawTerm

#check (@RawBlock.id : ∀ {Ty : Type uTy}, RawBlock Ty → BlockId)
#check (@RawBlock.params : ∀ {Ty : Type uTy}, RawBlock Ty → List Ty)
#check (@RawBlock.term : ∀ {Ty : Type uTy}, RawBlock Ty → RawTerm)

#check (@RawFlow.mk :
  ∀ {Ty : Type uTy},
    AlphabetId → List BlockId → BlockId → Ty → Ty →
      List (RawBlock Ty) → RawFlow Ty)
#check (@RawFlow.alphabet : ∀ {Ty : Type uTy}, RawFlow Ty → AlphabetId)
#check (@RawFlow.roots : ∀ {Ty : Type uTy}, RawFlow Ty → List BlockId)
#check (@RawFlow.entry : ∀ {Ty : Type uTy}, RawFlow Ty → BlockId)
#check (@RawFlow.inputTy : ∀ {Ty : Type uTy}, RawFlow Ty → Ty)
#check (@RawFlow.resultTy : ∀ {Ty : Type uTy}, RawFlow Ty → Ty)
#check (@RawFlow.blocks :
  ∀ {Ty : Type uTy}, RawFlow Ty → List (RawBlock Ty))

/-! D3: resolution, reachability, the cycle relations, and eight WF fields. -/

#check (@lookupBlock :
  ∀ {Ty : Type uTy}, RawFlow Ty → BlockId → Option (RawBlock Ty))

#check (@Edge :
  ∀ {Ty : Type uTy}, RawFlow Ty → BlockId → BlockId → Prop)

#check (@ReachableFrom :
  ∀ {Ty : Type uTy}, RawFlow Ty → BlockId → BlockId → Prop)

#check (@Reachable :
  ∀ {Ty : Type uTy}, RawFlow Ty → BlockId → Prop)

#check (@EntryReachable :
  ∀ {Ty : Type uTy}, RawFlow Ty → BlockId → Prop)

#check (@EdgeNoChoose :
  ∀ {Ty : Type uTy}, RawFlow Ty → BlockId → BlockId → Prop)

#check (@ReachableNoChoose :
  ∀ {Ty : Type uTy}, RawFlow Ty → BlockId → BlockId → Prop)

#check (@ReachableNoChoose.refl :
  ∀ {Ty : Type uTy} {raw : RawFlow Ty} (source : BlockId),
    ReachableNoChoose raw source source)

#check (@ReachableNoChoose.step :
  ∀ {Ty : Type uTy} {raw : RawFlow Ty} {source middle target : BlockId},
    ReachableNoChoose raw source middle →
    EdgeNoChoose raw middle target →
    ReachableNoChoose raw source target)

#check (@CyclesWF :
  ∀ {Ty : Type uTy}, RawFlow Ty → Prop)

#check (@cyclesChoose :
  ∀ {Ty : Type uTy}, RawFlow Ty → Bool)

#check (@cyclesChoose_iff :
  ∀ {Ty : Type uTy} {raw : RawFlow Ty},
    cyclesChoose raw = true ↔ CyclesWF raw)

#check (@AlphabetWF :
  ∀ {Ty : Type uTy},
    FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → Prop)

#check (@IdsWF :
  ∀ {Ty : Type uTy}, RawFlow Ty → Prop)

#check (@RootsWF :
  ∀ {Ty : Type uTy}, RawFlow Ty → Prop)

#check (@ReferencesWF :
  ∀ {Ty : Type uTy}, RawFlow Ty → Prop)

#check (@OperationsWF :
  ∀ {Ty : Type uTy},
    FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → Prop)

#check (@EntryWF :
  ∀ {Ty : Type uTy}, RawFlow Ty → Prop)

#check (@TermsWF :
  ∀ {Ty : Type uTy},
    FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → Prop)

#check (@FlowWF :
  ∀ {Ty : Type uTy},
    FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → Prop)

#check (@FlowWF.mk :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    AlphabetWF alphabet raw →
    IdsWF raw →
    RootsWF raw →
    ReferencesWF raw →
    OperationsWF alphabet raw →
    EntryWF raw →
    TermsWF alphabet raw →
    CyclesWF raw →
    FlowWF alphabet raw)

#check (@FlowWF.cycles :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    FlowWF alphabet raw → CyclesWF raw)

#check (@FlowWF.reachable_declared :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} (_wf : FlowWF alphabet raw) {target : BlockId},
    Reachable raw target → ∃ block, lookupBlock raw target = some block)

/-! D4: seventeen ordered clauses, sites, payloads, and exact witnesses. -/

#check (@AdmissionClause.alphabetMismatch : AdmissionClause)
#check (@AdmissionClause.duplicateBlockId : AdmissionClause)
#check (@AdmissionClause.duplicateDecisionId : AdmissionClause)
#check (@AdmissionClause.nonCanonicalBlockOrder : AdmissionClause)
#check (@AdmissionClause.emptyRoots : AdmissionClause)
#check (@AdmissionClause.duplicateRoot : AdmissionClause)
#check (@AdmissionClause.nonCanonicalRootOrder : AdmissionClause)
#check (@AdmissionClause.entryNotRoot : AdmissionClause)
#check (@AdmissionClause.danglingRoot : AdmissionClause)
#check (@AdmissionClause.danglingSuccessor : AdmissionClause)
#check (@AdmissionClause.unknownOperation : AdmissionClause)
#check (@AdmissionClause.entryTypeMismatch : AdmissionClause)
#check (@AdmissionClause.termTypeMismatch : AdmissionClause)
#check (@AdmissionClause.unknownVariable : AdmissionClause)
#check (@AdmissionClause.argumentArity : AdmissionClause)
#check (@AdmissionClause.argumentTypeMismatch : AdmissionClause)
#check (@AdmissionClause.unchosenCycle : AdmissionClause)
#synth DecidableEq AdmissionClause

#check (@scan : List AdmissionClause)

/-- The fixed scan order: the thirteen v1 clauses, then the four new ones. -/
example : scan = [
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
  ] := rfl

#check (@CheckSite.flow : CheckSite)
#check (@CheckSite.block : Nat → CheckSite)
#check (@CheckSite.decision : BlockId → CheckSite)
#check (@CheckSite.root : Nat → CheckSite)
#check (@CheckSite.successor : BlockId → Nat → CheckSite)
#check (@CheckSite.operation : BlockId → CheckSite)
#check (@CheckSite.entry : CheckSite)
#check (@CheckSite.term : BlockId → CheckSite)
#check (@CheckSite.argument : BlockId → Nat → Nat → CheckSite)
#synth DecidableEq CheckSite

#check (@DiagnosticPayload.none : ∀ {Ty : Type uTy}, DiagnosticPayload Ty)
#check (@DiagnosticPayload.alphabet :
  ∀ {Ty : Type uTy}, AlphabetId → AlphabetId → DiagnosticPayload Ty)
#check (@DiagnosticPayload.block :
  ∀ {Ty : Type uTy}, BlockId → DiagnosticPayload Ty)
#check (@DiagnosticPayload.decision :
  ∀ {Ty : Type uTy}, DecisionId → DiagnosticPayload Ty)
#check (@DiagnosticPayload.operation :
  ∀ {Ty : Type uTy}, OperationId → DiagnosticPayload Ty)
#check (@DiagnosticPayload.typeMismatch :
  ∀ {Ty : Type uTy}, Ty → Ty → DiagnosticPayload Ty)
#check (@DiagnosticPayload.variable :
  ∀ {Ty : Type uTy}, Var → DiagnosticPayload Ty)
#check (@DiagnosticPayload.arity :
  ∀ {Ty : Type uTy}, Nat → Nat → DiagnosticPayload Ty)

#check (@Diagnostic.mk :
  ∀ {Ty : Type uTy},
    AdmissionClause → CheckSite → DiagnosticPayload Ty → Diagnostic Ty)
#check (@Diagnostic.clause :
  ∀ {Ty : Type uTy}, Diagnostic Ty → AdmissionClause)
#check (@Diagnostic.site : ∀ {Ty : Type uTy}, Diagnostic Ty → CheckSite)
#check (@Diagnostic.payload :
  ∀ {Ty : Type uTy}, Diagnostic Ty → DiagnosticPayload Ty)

/-! D4a: the generic first failure in indexed source order (retained). -/

#check (@FirstFailureAt :
  {alpha : Type uA} → {beta : Type uB} →
  List alpha → (Nat → alpha → beta → Prop) →
  Nat → alpha → beta → Prop)

#check (@FirstFailureAt.mk :
  ∀ {alpha : Type uA} {beta : Type uB}
      {source : List alpha} {FailureAt : Nat → alpha → beta → Prop}
      {index : Nat} {item : alpha} {failure : beta},
    source[index]? = some item →
    FailureAt index item failure →
    (∀ priorIndex priorItem,
      priorIndex < index →
      source[priorIndex]? = some priorItem →
      ∀ priorFailure,
        ¬ FailureAt priorIndex priorItem priorFailure) →
    FirstFailureAt source FailureAt index item failure)

#check (@FirstFailureAt.source_at :
  ∀ {alpha : Type uA} {beta : Type uB}
      {source : List alpha} {FailureAt : Nat → alpha → beta → Prop}
      {index : Nat} {item : alpha} {failure : beta},
    FirstFailureAt source FailureAt index item failure →
    source[index]? = some item)

#check (@FirstFailureAt.fails_at :
  ∀ {alpha : Type uA} {beta : Type uB}
      {source : List alpha} {FailureAt : Nat → alpha → beta → Prop}
      {index : Nat} {item : alpha} {failure : beta},
    FirstFailureAt source FailureAt index item failure →
    FailureAt index item failure)

#check (@FirstFailureAt.prior_clear :
  ∀ {alpha : Type uA} {beta : Type uB}
      {source : List alpha} {FailureAt : Nat → alpha → beta → Prop}
      {index : Nat} {item : alpha} {failure : beta},
    FirstFailureAt source FailureAt index item failure →
    ∀ priorIndex priorItem,
      priorIndex < index →
      source[priorIndex]? = some priorItem →
      ∀ priorFailure,
        ¬ FailureAt priorIndex priorItem priorFailure)

/-! D4b: operand typing failures (clause `termTypeMismatch`), two forms. -/

#check (@TermFailureValid :
  {Ty : Type uTy} →
  FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → RawBlock Ty →
  DiagnosticPayload Ty → Prop)

/-! The ascriptions `(RawTerm.ret : Var → RawTerm)` and
`(RawTerm.choose : … → List Var → RawTerm)` below vanish after elaboration;
they name the v2 arity so that, while the carrier is v0.3.1, the hypothesis
fails at `Var` rather than at the constructor's v1 arity. -/

#check (@TermFailureValid.retTypeMismatch :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty} {value : Var} {actual : Ty},
    block.term = (RawTerm.ret : Var → RawTerm) value →
    (RawBlock.params block)[value.index]? = some actual →
    actual ≠ raw.resultTy →
    TermFailureValid alphabet raw block (.typeMismatch raw.resultTy actual))

#check (@TermFailureValid.performRequestTypeMismatch :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty}
      {operation : OperationId} {request : Var} {target : BlockId}
      {args : List Var} {operationDef : alphabet.Op} {actual : Ty},
    block.term = .perform operation request target args →
    alphabet.lookup operation = some operationDef →
    (RawBlock.params block)[request.index]? = some actual →
    actual ≠ alphabet.requestTy operationDef →
    TermFailureValid alphabet raw block
      (.typeMismatch (alphabet.requestTy operationDef) actual))

/-! D4c: positional typing failures on one successor edge
(clause `argumentTypeMismatch`), two forms. -/

#check (@ArgumentFailureValid :
  {Ty : Type uTy} →
  FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → RawBlock Ty → BlockId →
  Nat → DiagnosticPayload Ty → Prop)

#check (@ArgumentFailureValid.argument :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty} {target : BlockId}
      {targetBlock : RawBlock Ty} {position : Nat} {argument : Var}
      {supplied declared : Ty},
    lookupBlock raw target = some targetBlock →
    (RawTerm.args block.term)[position]? = some argument →
    (RawBlock.params block)[argument.index]? = some supplied →
    (RawBlock.params targetBlock)[position]? = some declared →
    supplied ≠ declared →
    ArgumentFailureValid alphabet raw block target position
      (.typeMismatch supplied declared))

#check (@ArgumentFailureValid.answer :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty} {target : BlockId}
      {operation : OperationId} {request : Var} {args : List Var}
      {operationDef : alphabet.Op} {targetBlock : RawBlock Ty} {declared : Ty},
    block.term = .perform operation request target args →
    alphabet.lookup operation = some operationDef →
    lookupBlock raw target = some targetBlock →
    (RawBlock.params targetBlock)[args.length]? = some declared →
    alphabet.answerTy operationDef ≠ declared →
    ArgumentFailureValid alphabet raw block target args.length
      (.typeMismatch (alphabet.answerTy operationDef) declared))

/-! D4d: exact site, payload, and source order for every diagnostic. -/

#check (@Diagnostic.Valid :
  {Ty : Type uTy} →
  FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → Diagnostic Ty → Prop)

#check (@Diagnostic.Valid.alphabetMismatch :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    raw.alphabet ≠ alphabet.id →
    Diagnostic.Valid alphabet raw
      { clause := .alphabetMismatch
        site := .flow
        payload := .alphabet alphabet.id raw.alphabet })

#check (@Diagnostic.Valid.duplicateBlockId :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty},
    FirstFailureAt raw.blocks
      (fun candidateIndex candidate reported =>
        reported = candidate.id ∧
        candidate.id ∈
          (raw.blocks.take candidateIndex).map RawBlock.id)
      index block block.id →
    Diagnostic.Valid alphabet raw
      { clause := .duplicateBlockId
        site := .block index
        payload := .block block.id })

#check (@Diagnostic.Valid.duplicateDecisionId :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty}
      {decision : DecisionId},
    FirstFailureAt raw.blocks
      (fun candidateIndex candidate reported =>
        ∃ (left right : BlockId) (args : List Var),
          candidate.term =
            (RawTerm.choose : DecisionId → BlockId → BlockId → List Var → RawTerm)
              reported left right args ∧
          reported ∈
            (raw.blocks.take candidateIndex).filterMap
              (fun prior => RawTerm.decision? prior.term))
      index block decision →
    Diagnostic.Valid alphabet raw
      { clause := .duplicateDecisionId
        site := .decision block.id
        payload := .decision decision })

#check (@Diagnostic.Valid.nonCanonicalBlockOrder :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty},
    FirstFailureAt raw.blocks
      (fun candidateIndex candidate reported =>
        reported = candidate.id ∧ 0 < candidateIndex ∧
        ∃ previous,
          raw.blocks[candidateIndex - 1]? = some previous ∧
          ¬ (previous.id.value < candidate.id.value))
      index block block.id →
    Diagnostic.Valid alphabet raw
      { clause := .nonCanonicalBlockOrder
        site := .block index
        payload := .block block.id })

#check (@Diagnostic.Valid.emptyRoots :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    raw.roots = [] →
    Diagnostic.Valid alphabet raw
      { clause := .emptyRoots, site := .flow, payload := .none })

#check (@Diagnostic.Valid.duplicateRoot :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {root : BlockId},
    FirstFailureAt raw.roots
      (fun candidateIndex candidate reported =>
        reported = candidate ∧
        candidate ∈ raw.roots.take candidateIndex)
      index root root →
    Diagnostic.Valid alphabet raw
      { clause := .duplicateRoot
        site := .root index
        payload := .block root })

#check (@Diagnostic.Valid.nonCanonicalRootOrder :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {root : BlockId},
    FirstFailureAt raw.roots
      (fun candidateIndex candidate reported =>
        reported = candidate ∧ 0 < candidateIndex ∧
        ∃ previous,
          raw.roots[candidateIndex - 1]? = some previous ∧
          ¬ (previous.value < candidate.value))
      index root root →
    Diagnostic.Valid alphabet raw
      { clause := .nonCanonicalRootOrder
        site := .root index
        payload := .block root })

#check (@Diagnostic.Valid.entryNotRoot :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    raw.entry ∉ raw.roots →
    Diagnostic.Valid alphabet raw
      { clause := .entryNotRoot
        site := .entry
        payload := .block raw.entry })

#check (@Diagnostic.Valid.danglingRoot :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {root : BlockId},
    FirstFailureAt raw.roots
      (fun _ candidate reported =>
        reported = candidate ∧ lookupBlock raw candidate = none)
      index root root →
    Diagnostic.Valid alphabet raw
      { clause := .danglingRoot
        site := .root index
        payload := .block root })

#check (@Diagnostic.Valid.danglingSuccessor :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {blockIndex successorIndex : Nat}
      {block : RawBlock Ty} {target : BlockId},
    FirstFailureAt raw.blocks
      (fun _ candidate witness =>
        FirstFailureAt candidate.term.successors
          (fun _ successor reported =>
            reported = successor ∧ lookupBlock raw successor = none)
          witness.1 witness.2 witness.2)
      blockIndex block (successorIndex, target) →
    Diagnostic.Valid alphabet raw
      { clause := .danglingSuccessor
        site := .successor block.id successorIndex
        payload := .block target })

#check (@Diagnostic.Valid.unknownOperation :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty}
      {operation : OperationId},
    FirstFailureAt raw.blocks
      (fun _ candidate reported =>
        ∃ (request : Var) (target : BlockId) (args : List Var),
          candidate.term = .perform reported request target args ∧
          alphabet.lookup reported = none)
      index block operation →
    Diagnostic.Valid alphabet raw
      { clause := .unknownOperation
        site := .operation block.id
        payload := .operation operation })

#check (@Diagnostic.Valid.entryMissing :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty},
    lookupBlock raw raw.entry = none →
    Diagnostic.Valid alphabet raw
      { clause := .entryTypeMismatch
        site := .entry
        payload := .block raw.entry })

#check (@Diagnostic.Valid.entryArity :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty},
    lookupBlock raw raw.entry = some block →
    List.length (RawBlock.params block) ≠ 1 →
    Diagnostic.Valid alphabet raw
      { clause := .entryTypeMismatch
        site := .entry
        payload := .arity 1 (List.length (RawBlock.params block)) })

#check (@Diagnostic.Valid.entryTypeMismatch :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {block : RawBlock Ty} {actual : Ty},
    lookupBlock raw raw.entry = some block →
    RawBlock.params block = [actual] →
    actual ≠ raw.inputTy →
    Diagnostic.Valid alphabet raw
      { clause := .entryTypeMismatch
        site := .entry
        payload := .typeMismatch raw.inputTy actual })

#check (@Diagnostic.Valid.termTypeMismatch :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty}
      {payload : DiagnosticPayload Ty},
    FirstFailureAt raw.blocks
      (fun _ candidate failure =>
        TermFailureValid alphabet raw candidate failure)
      index block payload →
    Diagnostic.Valid alphabet raw
      { clause := .termTypeMismatch
        site := .term block.id
        payload := payload })

#check (@Diagnostic.Valid.unknownVariable :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {blockIndex operandIndex : Nat}
      {block : RawBlock Ty} {unknown : Var},
    FirstFailureAt raw.blocks
      (fun _ candidate witness =>
        FirstFailureAt (RawTerm.operands candidate.term)
          (fun _ operand reported =>
            reported = operand ∧
            List.length (RawBlock.params candidate) ≤ operand.index)
          witness.1 witness.2 witness.2)
      blockIndex block (operandIndex, unknown) →
    Diagnostic.Valid alphabet raw
      { clause := .unknownVariable
        site := .term block.id
        payload := .variable unknown })

#check (@Diagnostic.Valid.argumentArity :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {blockIndex successorIndex : Nat}
      {block : RawBlock Ty} {target : BlockId} {declared : Nat},
    FirstFailureAt raw.blocks
      (fun _ candidate witness =>
        FirstFailureAt candidate.term.successors
          (fun _ successor reported =>
            ∃ targetBlock : RawBlock Ty,
              lookupBlock raw successor = some targetBlock ∧
              List.length (RawBlock.params targetBlock) = reported ∧
              reported ≠ RawTerm.arity candidate.term)
          witness.1 witness.2.1 witness.2.2)
      blockIndex block (successorIndex, target, declared) →
    Diagnostic.Valid alphabet raw
      { clause := .argumentArity
        site := .successor block.id successorIndex
        payload := .arity (RawTerm.arity block.term) declared })

#check (@Diagnostic.Valid.argumentTypeMismatch :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {blockIndex successorIndex position : Nat}
      {block : RawBlock Ty} {target : BlockId}
      {payload : DiagnosticPayload Ty},
    FirstFailureAt raw.blocks
      (fun _ candidate witness =>
        FirstFailureAt candidate.term.successors
          (fun _ successor edge =>
            FirstFailureAt (List.range (RawTerm.arity candidate.term))
              (fun _ slot failure =>
                ArgumentFailureValid alphabet raw candidate successor slot failure)
              edge.1 edge.1 edge.2)
          witness.1 witness.2.1 witness.2.2)
      blockIndex block (successorIndex, target, (position, payload)) →
    Diagnostic.Valid alphabet raw
      { clause := .argumentTypeMismatch
        site := .argument block.id successorIndex position
        payload := payload })

#check (@Diagnostic.Valid.unchosenCycle :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {raw : RawFlow Ty} {index : Nat} {block : RawBlock Ty},
    FirstFailureAt raw.blocks
      (fun _ candidate reported =>
        reported = candidate.id ∧
        ∃ next : BlockId,
          EdgeNoChoose raw candidate.id next ∧
          ReachableNoChoose raw next candidate.id)
      index block block.id →
    Diagnostic.Valid alphabet raw
      { clause := .unchosenCycle
        site := .block index
        payload := .block block.id })

/-! D5: admission (retained shapes over the new carrier). -/

#check (@diagnoseAt :
  ∀ {Ty : Type uTy} [DecidableEq Ty],
    FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → AdmissionClause →
      Option (Diagnostic Ty))

#check (@FirstDiagnostic :
  ∀ {Ty : Type uTy} [DecidableEq Ty],
    FlowAlphabet.{uTy, uOp} Ty → RawFlow Ty → Diagnostic Ty → Prop)

#check (@FirstDiagnostic.mk :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    diagnoseAt alphabet raw diagnostic.clause = some diagnostic →
    (∀ clause,
      clause ∈ scan.takeWhile
        (fun candidate => decide (candidate != diagnostic.clause)) →
      diagnoseAt alphabet raw clause = none) →
    FirstDiagnostic alphabet raw diagnostic)

#check (@FirstDiagnostic.condemns :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    FirstDiagnostic alphabet raw diagnostic →
      diagnoseAt alphabet raw diagnostic.clause = some diagnostic)

#check (@CheckedFlow :
  ∀ {Ty : Type uTy}, FlowAlphabet.{uTy, uOp} Ty → Type uTy)

#check (@CheckedFlow.raw :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty},
    CheckedFlow alphabet → RawFlow Ty)

#check (@CheckedFlow.wf :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      (checked : CheckedFlow alphabet),
    FlowWF alphabet checked.raw)

#check (@CheckedFlow.erase :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty},
    CheckedFlow alphabet → RawFlow Ty)

#check (@admit :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      (alphabet : FlowAlphabet.{uTy, uOp} Ty) (_raw : RawFlow Ty),
    Except (Diagnostic Ty) (CheckedFlow alphabet))

/-! ENSURES: the retained theorem shapes and the new checker law. -/

#check (@admit_sound :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {checked : CheckedFlow alphabet},
    admit alphabet raw = .ok checked → FlowWF alphabet raw)

#check (@admit_complete :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty},
    FlowWF alphabet raw →
      ∃ checked : CheckedFlow alphabet, admit alphabet raw = .ok checked)

#check (@error_iff_not_wf :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty},
    (∃ diagnostic : Diagnostic Ty,
      admit alphabet raw = .error diagnostic) ↔
    ¬ FlowWF alphabet raw)

#check (@error_iff_firstDiagnostic :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    admit alphabet raw = .error diagnostic ↔
      FirstDiagnostic alphabet raw diagnostic)

#check (@admit_error_valid :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    admit alphabet raw = .error diagnostic →
    Diagnostic.Valid alphabet raw diagnostic)

#check (@diagnoseAt_some_valid :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {clause : AdmissionClause} {diagnostic : Diagnostic Ty},
    diagnoseAt alphabet raw clause = some diagnostic →
    Diagnostic.Valid alphabet raw diagnostic)

#check (@FirstDiagnostic.valid :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {diagnostic : Diagnostic Ty},
    FirstDiagnostic alphabet raw diagnostic →
    Diagnostic.Valid alphabet raw diagnostic)

#check (@Diagnostic.clause_all_complete :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty},
    FlowWF alphabet raw ↔
      ∀ clause, clause ∈ scan → diagnoseAt alphabet raw clause = none)

#check (@erase_wf :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      (checked : CheckedFlow alphabet),
    FlowWF alphabet checked.erase)

#check (@erase_admit :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty} {raw : RawFlow Ty}
      {checked : CheckedFlow alphabet},
    admit alphabet raw = .ok checked → checked.erase = raw)

#check (@admit_erase :
  ∀ {Ty : Type uTy} [DecidableEq Ty]
      {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      (checked : CheckedFlow alphabet),
    admit alphabet checked.erase = .ok checked)

#check (@CheckedFlow.erase_eq_raw :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      (checked : CheckedFlow alphabet),
    checked.erase = checked.raw)

#check (@CheckedFlow.ext :
  ∀ {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
      {left right : CheckedFlow alphabet},
    left.raw = right.raw → left = right)

end SurfaceSnapshot

/-! ## Definitional receipts

Kernel-checked facts about the frozen bodies. Each statement is headed by a
frozen v2 name, so its v2-shaped literal is never elaborated against the
v0.3.1 carrier. -/

section Receipts

/-- Two type codes: enough for `get : unit → nat` and `put : nat → unit`. -/
inductive TyCode where
  | nat
  | unit
deriving DecidableEq, Repr

inductive ExampleOp where
  | get
  | put
deriving DecidableEq, Repr

def blockId (value : Nat) : BlockId := ⟨value⟩
def operationId (value : Nat) : OperationId := ⟨value⟩
def alphabetId (value : Nat) : AlphabetId := ⟨value⟩
def decisionId (value : Nat) : DecisionId := ⟨value⟩

def exampleLookup : OperationId → Option ExampleOp
  | ⟨0⟩ => some .get
  | ⟨1⟩ => some .put
  | _ => none

/-- `get : unit → nat` is operation 0; `put : nat → unit` is operation 1. -/
def ExampleAlphabet : FlowAlphabet TyCode where
  id := alphabetId 7
  Op := ExampleOp
  operationId
    | .get => operationId 0
    | .put => operationId 1
  lookup := exampleLookup
  requestTy
    | .get => .unit
    | .put => .nat
  answerTy
    | .get => .nat
    | .put => .unit
  lookup_operationId := by
    intro operation
    cases operation <;> rfl
  operationId_of_lookup := by
    intro id operation found
    cases operation <;> rcases id with ⟨_ | _ | value⟩ <;>
      simp [exampleLookup] at found <;> rfl

/-- `RawTerm.args`: the argument list every successor receives. -/
example :
    RawTerm.args (.ret ⟨0⟩) = ([] : List Var) ∧
    RawTerm.args (.jump (blockId 1) [⟨0⟩, ⟨1⟩]) = ([⟨0⟩, ⟨1⟩] : List Var) ∧
    RawTerm.args (.perform (operationId 0) ⟨2⟩ (blockId 1) [⟨0⟩, ⟨1⟩]) =
      ([⟨0⟩, ⟨1⟩] : List Var) ∧
    RawTerm.args (.choose (decisionId 0) (blockId 1) (blockId 2) [⟨0⟩, ⟨1⟩]) =
      ([⟨0⟩, ⟨1⟩] : List Var) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `RawTerm.operands`: every variable occurrence in source order; a
`perform` names its request before its arguments. -/
example :
    RawTerm.operands (.ret ⟨0⟩) = ([⟨0⟩] : List Var) ∧
    RawTerm.operands (.jump (blockId 1) [⟨0⟩, ⟨1⟩]) = ([⟨0⟩, ⟨1⟩] : List Var) ∧
    RawTerm.operands (.perform (operationId 0) ⟨2⟩ (blockId 1) [⟨0⟩, ⟨1⟩]) =
      ([⟨2⟩, ⟨0⟩, ⟨1⟩] : List Var) ∧
    RawTerm.operands (.choose (decisionId 0) (blockId 1) (blockId 2) [⟨0⟩, ⟨1⟩]) =
      ([⟨0⟩, ⟨1⟩] : List Var) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `RawTerm.arity`: the number of values every successor receives; a
`perform` adds the answer. -/
example :
    RawTerm.arity (.ret ⟨0⟩) = 0 ∧
    RawTerm.arity (.jump (blockId 1) [⟨0⟩, ⟨1⟩]) = 2 ∧
    RawTerm.arity (.perform (operationId 0) ⟨2⟩ (blockId 1) [⟨0⟩, ⟨1⟩]) = 3 ∧
    RawTerm.arity (.choose (decisionId 0) (blockId 1) (blockId 2) [⟨0⟩, ⟨1⟩]) = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `RawTerm.isChoose`: only `choose` is a decision. -/
example :
    RawTerm.isChoose (.ret ⟨0⟩) = false ∧
    RawTerm.isChoose (.jump (blockId 1) [⟨0⟩]) = false ∧
    RawTerm.isChoose (.perform (operationId 0) ⟨0⟩ (blockId 1) [⟨0⟩]) = false ∧
    RawTerm.isChoose (.choose (decisionId 0) (blockId 1) (blockId 2) [⟨0⟩]) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `RawTerm.decision?`: the decision of a `choose`, and the projection
`duplicateDecisionId` scans with. -/
example :
    RawTerm.decision? (.ret ⟨0⟩) = none ∧
    RawTerm.decision? (.jump (blockId 1) [⟨0⟩]) = none ∧
    RawTerm.decision? (.perform (operationId 0) ⟨0⟩ (blockId 1) [⟨0⟩]) = none ∧
    RawTerm.decision? (.choose (decisionId 4) (blockId 1) (blockId 2) [⟨0⟩]) =
      some (decisionId 4) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `RawBlock.mk` in field order: identity, parameter types, terminator. -/
example :
    RawBlock.params
      (RawBlock.mk (blockId 2) [TyCode.nat, TyCode.unit] (.ret ⟨0⟩)) =
      [TyCode.nat, TyCode.unit] :=
  rfl

/-- `EntryWF`: the entry resolves and its parameter list is exactly `[inputTy]`. -/
example {raw : RawFlow TyCode} :
    EntryWF raw ↔
      (match lookupBlock raw raw.entry with
        | none => False
        | some block => RawBlock.params block = [raw.inputTy]) :=
  Iff.rfl

/-- `EdgeNoChoose`: a declared edge whose source block is not a `choose`. -/
example {raw : RawFlow TyCode} {source target : BlockId} :
    EdgeNoChoose raw source target ↔
      ∃ block, block ∈ raw.blocks ∧ block.id = source ∧
        RawTerm.isChoose block.term = false ∧
        target ∈ block.term.successors :=
  Iff.rfl

/-- `CyclesWF`: no `EdgeNoChoose` closes into a `ReachableNoChoose` cycle. -/
example {raw : RawFlow TyCode} :
    CyclesWF raw ↔
      ∀ source target, EdgeNoChoose raw source target →
        ReachableNoChoose raw target source → False :=
  Iff.rfl

/-! ### Concrete flows

Written as local notation so that each literal appears only as an argument
of a frozen v2 name. The same flows are `def`s in
`EffectsTest/Counterexamples/Flow/FlowV2.lean`, where `admit` runs on them. -/

set_option quotPrecheck false in
/-- The `incr` shape: `get` answers into a fresh parameter; `put` consumes
that parameter as its request while the entry parameter and the answer are
both passed on; the final block returns the answer of `get`. A value
therefore crosses a `perform`, which v1's single payload could not express. -/
local notation "incr" =>
  (RawFlow.mk (alphabetId 7) [blockId 0] (blockId 0) TyCode.unit TyCode.nat [
    RawBlock.mk (blockId 0) [TyCode.unit]
      (RawTerm.perform (operationId 0) ⟨0⟩ (blockId 1) [⟨0⟩]),
    RawBlock.mk (blockId 1) [TyCode.unit, TyCode.nat]
      (RawTerm.perform (operationId 1) ⟨1⟩ (blockId 2) [⟨0⟩, ⟨1⟩]),
    RawBlock.mk (blockId 2) [TyCode.unit, TyCode.nat, TyCode.unit]
      (RawTerm.ret ⟨1⟩)] : RawFlow TyCode)

set_option quotPrecheck false in
/-- A `jump` to itself: the cycle passes through no `choose`. -/
local notation "unchosenLoop" =>
  (RawFlow.mk (alphabetId 7) [blockId 0] (blockId 0) TyCode.unit TyCode.unit [
    RawBlock.mk (blockId 0) [TyCode.unit]
      (RawTerm.jump (blockId 0) [⟨0⟩])] : RawFlow TyCode)

set_option quotPrecheck false in
/-- A `choose` whose left branch is itself: the cycle passes through a decision. -/
local notation "chosenLoop" =>
  (RawFlow.mk (alphabetId 7) [blockId 0] (blockId 0) TyCode.unit TyCode.unit [
    RawBlock.mk (blockId 0) [TyCode.unit]
      (RawTerm.choose (decisionId 0) (blockId 0) (blockId 1) [⟨0⟩]),
    RawBlock.mk (blockId 1) [TyCode.unit] (RawTerm.ret ⟨0⟩)] : RawFlow TyCode)

set_option quotPrecheck false in
/-- A two-block cycle through `get`: a `perform` edge is not a decision. -/
local notation "performLoop" =>
  (RawFlow.mk (alphabetId 7) [blockId 0] (blockId 0) TyCode.unit TyCode.unit [
    RawBlock.mk (blockId 0) [TyCode.unit]
      (RawTerm.perform (operationId 0) ⟨0⟩ (blockId 1) [⟨0⟩]),
    RawBlock.mk (blockId 1) [TyCode.unit, TyCode.nat]
      (RawTerm.jump (blockId 0) [⟨0⟩])] : RawFlow TyCode)

/-- The parameter list of the block after `put` holds the entry parameter,
the answer of `get`, and the answer of `put`, in that order. -/
example :
    RawBlock.params
      (RawBlock.mk (blockId 2) [TyCode.unit, TyCode.nat, TyCode.unit]
        (RawTerm.ret ⟨1⟩)) =
      [TyCode.unit, TyCode.nat, TyCode.unit] :=
  rfl

/-- The checker is kernel-computable (REQUIRES 4) and accepts `incr`. -/
example : cyclesChoose incr = true := by decide

/-- `CyclesWF` for a concrete flow follows from the checker by `decide`. -/
example : CyclesWF incr := cyclesChoose_iff.mp (by decide)

example : cyclesChoose chosenLoop = true := by decide

example : CyclesWF chosenLoop := cyclesChoose_iff.mp (by decide)

example : cyclesChoose unchosenLoop = false := by decide

/-- The self-loop is an `EdgeNoChoose` from block 0 to itself, closed by
`ReachableNoChoose.refl`. This is the kernel receipt behind the
`unchosenCycle` diagnostic that `EffectsTest/Counterexamples/Flow/FlowV2.lean`
observes from `admit`. -/
example : ¬ CyclesWF unchosenLoop := fun wf =>
  wf (blockId 0) (blockId 0)
    (show ∃ block, block ∈ (unchosenLoop).blocks ∧ block.id = blockId 0 ∧
        RawTerm.isChoose block.term = false ∧ blockId 0 ∈ block.term.successors
      from ⟨_, List.Mem.head _, rfl, rfl, List.Mem.head _⟩)
    (.refl _)

example : cyclesChoose performLoop = false := by decide

/-- Block 0 reaches block 1 through `get` and block 1 jumps back: two
`EdgeNoChoose` steps and no decision. -/
example : ¬ CyclesWF performLoop := fun wf =>
  wf (blockId 0) (blockId 1)
    (show ∃ block, block ∈ (performLoop).blocks ∧ block.id = blockId 0 ∧
        RawTerm.isChoose block.term = false ∧ blockId 1 ∈ block.term.successors
      from ⟨_, List.Mem.head _, rfl, rfl, List.Mem.head _⟩)
    (.step (.refl _)
      (show ∃ block, block ∈ (performLoop).blocks ∧ block.id = blockId 1 ∧
          RawTerm.isChoose block.term = false ∧ blockId 0 ∈ block.term.successors
        from ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, rfl, List.Mem.head _⟩))

end Receipts

/-! ## Retained v1 receipts -/

/-! E4-FLOW-CE-015 (retained): the checked constructor stays private, so an
importing module cannot build a `CheckedFlow` without `admit`. -/

/--
error: Unknown constant
-/
#guard_msgs(error, substring := true) in
#check (@CheckedFlow.mk)

section RecordLiteral

variable {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
variable (raw : RawFlow Ty) (wf : FlowWF alphabet raw)

/--
error: invalid {...} notation, constructor for `CheckedFlow` is marked as private
-/
#guard_msgs(error, substring := true) in
#check ({ raw := raw, wf := wf } : CheckedFlow alphabet)

end RecordLiteral

/-! E4-FLOW-CE-013 (retained): a Lean function is not a block identifier;
canonical content carries no host continuation. -/

/--
error: Application type mismatch
-/
#guard_msgs(error, substring := true) in
#check (RawTerm.choose (decisionId 0)
  (fun _ : Bool => blockId 1) (blockId 2) ([] : List Var))

end EffectsTest.Flow.FlowV2Contract
