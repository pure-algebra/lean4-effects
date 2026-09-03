import Effects.Flow.Block

/-!
# Raw first-order flows

Raw flows retain graph identity, sharing, cycles, and unreachable declarations.
The eight well-formedness clauses below check the entire declared document;
none adds reachability coverage. The one global clause, `CyclesWF`, says every
cycle of the successor graph passes through a `choose`, so a finite decision
tape bounds every run; `cyclesChoose` decides it by structural recursion and
`cyclesChoose_iff` is its law (`test/contracts/flow-v2.contract.md`).
-/

namespace Effects

/-- Unchecked, canonicalizable first-order effect-flow input. -/
structure RawFlow (Ty : Type uTy) where
  alphabet : AlphabetId
  roots : List BlockId
  entry : BlockId
  inputTy : Ty
  resultTy : Ty
  blocks : List (RawBlock Ty)
deriving DecidableEq, Repr

/-- Resolve the first declared block with the requested nominal identity. -/
def lookupBlock (raw : RawFlow Ty) (id : BlockId) : Option (RawBlock Ty) :=
  raw.blocks.find? fun block => block.id = id

/-- A declared block directly names `target` as one of its successors. -/
def Edge (raw : RawFlow Ty) (source target : BlockId) : Prop :=
  ∃ block, block ∈ raw.blocks ∧ block.id = source ∧
    target ∈ block.term.successors

/-- Reflexive-transitive reachability through declared successor edges. -/
inductive ReachableFrom (raw : RawFlow Ty) : BlockId → BlockId → Prop where
  | refl (source : BlockId) : ReachableFrom raw source source
  | step {source middle target : BlockId} :
      ReachableFrom raw source middle →
      Edge raw middle target →
      ReachableFrom raw source target

/-- Reachability from any declared root. -/
def Reachable (raw : RawFlow Ty) (target : BlockId) : Prop :=
  ∃ root, root ∈ raw.roots ∧ ReachableFrom raw root target

/-- Reachability from the distinguished entry block. -/
def EntryReachable (raw : RawFlow Ty) (target : BlockId) : Prop :=
  ReachableFrom raw raw.entry target

/-- The raw document names the supplied closed alphabet. -/
def AlphabetWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop :=
  raw.alphabet = alphabet.id

private def decisionIds (raw : RawFlow Ty) : List DecisionId :=
  raw.blocks.filterMap fun block => block.term.decision?

/--
Block identities are unique and strictly ascending, and decision identities
are globally unique across all declared blocks, reachable or otherwise.
-/
def IdsWF (raw : RawFlow Ty) : Prop :=
  (raw.blocks.map RawBlock.id).Nodup ∧
  raw.blocks.Pairwise
    (fun left right => left.id.value < right.id.value) ∧
  (decisionIds raw).Nodup

/--
Roots form a nonempty, unique, strictly ascending table containing the entry,
and every root resolves in the declared block table.
-/
def RootsWF (raw : RawFlow Ty) : Prop :=
  raw.roots ≠ [] ∧
  raw.roots.Nodup ∧
  raw.roots.Pairwise (fun left right => left.value < right.value) ∧
  raw.entry ∈ raw.roots ∧
  ∀ root, root ∈ raw.roots → (lookupBlock raw root).isSome = true

/-- Every successor in every declared block resolves, including unreachable blocks. -/
def ReferencesWF (raw : RawFlow Ty) : Prop :=
  ∀ block, block ∈ raw.blocks →
    ∀ target, target ∈ block.term.successors →
      (lookupBlock raw target).isSome = true

/-- A performed operation belongs to the alphabet. -/
def OperationWF (alphabet : FlowAlphabet Ty) (block : RawBlock Ty) : Prop :=
  match block.term with
  | .perform operation _ _ _ => (alphabet.lookup operation).isSome = true
  | _ => True

/-- Every performed operation in every declared block belongs to the alphabet. -/
def OperationsWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop :=
  ∀ block, block ∈ raw.blocks → OperationWF alphabet block

/-- The distinguished entry resolves and its parameter list is exactly the
document input type. -/
def EntryWF (raw : RawFlow Ty) : Prop :=
  match lookupBlock raw raw.entry with
  | none => False
  | some block => block.params = [raw.inputTy]

/-! ## The four term clauses -/

/-- Every operand of a block names one of its parameters. -/
def RawBlock.VarsWF (block : RawBlock Ty) : Prop :=
  ∀ v, v ∈ block.term.operands → v.index < block.params.length

/-- Every resolving successor declares exactly as many parameters as the
terminator supplies. -/
def ArityWF (raw : RawFlow Ty) (block : RawBlock Ty) : Prop :=
  ∀ target, target ∈ block.term.successors →
    match lookupBlock raw target with
    | none => True
    | some targetBlock => targetBlock.params.length = block.term.arity

/-- One value position on one successor edge is well typed: an argument's
parameter type equals the declared type at that position, and a `perform`'s
answer slot equals the operation's answer type. Guarded by resolution,
arity, variable range, and operation closure, which other clauses own. -/
def SlotWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) (block : RawBlock Ty)
    (target : BlockId) (slot : Nat) : Prop :=
  match lookupBlock raw target with
  | none => True
  | some targetBlock =>
    match block.term.args[slot]? with
    | some argument =>
        match block.params[argument.index]?, targetBlock.params[slot]? with
        | some supplied, some declared => supplied = declared
        | _, _ => True
    | none =>
        match block.term with
        | .perform operation _ performTarget args =>
            if slot = args.length ∧ performTarget = target then
              match alphabet.lookup operation, targetBlock.params[slot]? with
              | some operationDef, some declared => alphabet.answerTy operationDef = declared
              | _, _ => True
            else True
        | _ => True

/-- Every position of every successor edge of a block is well typed. -/
def ArgumentsWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) (block : RawBlock Ty) : Prop :=
  ∀ target, target ∈ block.term.successors →
    ∀ slot, slot ∈ List.range block.term.arity → SlotWF alphabet raw block target slot

/-- A `ret` returns the document result type and a `perform` request has the
operation's request type, guarded by variable range and operation closure. -/
def OperandsWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) (block : RawBlock Ty) : Prop :=
  match block.term with
  | .ret value =>
      match block.params[value.index]? with
      | some actual => actual = raw.resultTy
      | none => True
  | .perform operation request _ _ =>
      match alphabet.lookup operation, block.params[request.index]? with
      | some operationDef, some actual => actual = alphabet.requestTy operationDef
      | _, _ => True
  | _ => True

/-- Every declared block satisfies the four term clauses: variables in range,
successor arity, argument and answer types, and operand types. -/
def TermsWF (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop :=
  (∀ block, block ∈ raw.blocks → block.VarsWF) ∧
  (∀ block, block ∈ raw.blocks → ArityWF raw block) ∧
  (∀ block, block ∈ raw.blocks → ArgumentsWF alphabet raw block) ∧
  (∀ block, block ∈ raw.blocks → OperandsWF alphabet raw block)

/-! ## The cycle clause -/

/-- A declared edge whose source block is not a `choose`. -/
def EdgeNoChoose (raw : RawFlow Ty) (source target : BlockId) : Prop :=
  ∃ block, block ∈ raw.blocks ∧ block.id = source ∧
    block.term.isChoose = false ∧ target ∈ block.term.successors

/-- Reflexive-transitive closure of `EdgeNoChoose`. -/
inductive ReachableNoChoose (raw : RawFlow Ty) : BlockId → BlockId → Prop where
  | refl (source : BlockId) : ReachableNoChoose raw source source
  | step {source middle target : BlockId} :
      ReachableNoChoose raw source middle →
      EdgeNoChoose raw middle target →
      ReachableNoChoose raw source target

/-- Every cycle of the successor graph passes through a `choose` block. -/
def CyclesWF (raw : RawFlow Ty) : Prop :=
  ∀ source target, EdgeNoChoose raw source target →
    ReachableNoChoose raw target source → False

/-- Exactly the eight independent admission clauses for a raw flow. -/
structure FlowWF (alphabetDef : FlowAlphabet Ty) (raw : RawFlow Ty) : Prop where
  alphabet : AlphabetWF alphabetDef raw
  ids : IdsWF raw
  roots : RootsWF raw
  references : ReferencesWF raw
  operations : OperationsWF alphabetDef raw
  entry : EntryWF raw
  terms : TermsWF alphabetDef raw
  cycles : CyclesWF raw

private theorem exists_eq_some_of_isSome
    {value : Option α} (isSome : value.isSome = true) :
    ∃ item, value = some item := by
  cases value with
  | none => cases isSome
  | some item => exact ⟨item, rfl⟩

namespace FlowWF

/-- Every block reachable from a root resolves in the declared block table. -/
theorem reachable_declared
    {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) {target : BlockId} :
    Reachable raw target → ∃ block, lookupBlock raw target = some block := by
  rintro ⟨root, rootMem, path⟩
  have rootIsSome : (lookupBlock raw root).isSome = true :=
    wf.roots.2.2.2.2 root rootMem
  have rootDeclared : ∃ block, lookupBlock raw root = some block :=
    exists_eq_some_of_isSome rootIsSome
  induction path with
  | refl => exact rootDeclared
  | step _ edge _ =>
      rcases edge with ⟨block, blockMem, _, targetMem⟩
      exact exists_eq_some_of_isSome
        (wf.references block blockMem _ targetMem)

end FlowWF

/-! ## The decidable cycle checker

`reachSet raw start` saturates the set of blocks reachable from `start`
through non-`choose` edges. It is structural recursion on a fuel that exceeds
the number of declared successor targets, so it is kernel-computable and
`decide` closes `cyclesChoose raw = true` on a concrete flow. -/

namespace RawFlow

/-- The targets of every non-`choose` declared block named `source`. -/
def noChooseSuccessors (raw : RawFlow Ty) (source : BlockId) : List BlockId :=
  (raw.blocks.filter fun block => decide (block.id = source) && !block.term.isChoose).flatMap
    fun block => block.term.successors

private theorem bnot_eq_true_iff (b : Bool) : (!b) = true ↔ b = false := by
  cases b <;> simp

theorem mem_noChooseSuccessors {raw : RawFlow Ty} {source target : BlockId} :
    target ∈ raw.noChooseSuccessors source ↔ EdgeNoChoose raw source target := by
  constructor
  · intro mem
    obtain ⟨block, blockMem, targetMem⟩ := List.mem_flatMap.mp mem
    obtain ⟨mem', pass⟩ := List.mem_filter.mp blockMem
    obtain ⟨idEq, notChoose⟩ := Bool.and_eq_true_iff.mp pass
    exact ⟨block, mem', of_decide_eq_true idEq, (bnot_eq_true_iff _).mp notChoose, targetMem⟩
  · rintro ⟨block, mem, idEq, notChoose, targetMem⟩
    apply List.mem_flatMap.mpr
    refine ⟨block, List.mem_filter.mpr ⟨mem, ?_⟩, targetMem⟩
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true idEq, (bnot_eq_true_iff _).mpr notChoose⟩

/-- Every successor of every declared block. -/
def allSuccessors (raw : RawFlow Ty) : List BlockId :=
  raw.blocks.flatMap fun block => block.term.successors

theorem noChooseSuccessors_subset (raw : RawFlow Ty) (source : BlockId) :
    raw.noChooseSuccessors source ⊆ raw.allSuccessors := by
  intro target mem
  obtain ⟨block, blockMem, _, _, targetMem⟩ := mem_noChooseSuccessors.mp mem
  exact List.mem_flatMap.mpr ⟨block, blockMem, targetMem⟩

/-- Append each element not already present, in order. -/
def insertAll (set : List BlockId) : List BlockId → List BlockId
  | [] => set
  | x :: xs => insertAll (if x ∈ set then set else set ++ [x]) xs

theorem mem_insertAll {set xs : List BlockId} {x : BlockId} :
    x ∈ insertAll set xs ↔ x ∈ set ∨ x ∈ xs := by
  induction xs generalizing set with
  | nil => simp [insertAll]
  | cons y ys ih =>
      simp only [insertAll]
      by_cases mem : y ∈ set
      · rw [if_pos mem, ih]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
        · rintro (h | h)
          · exact Or.inl h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inl mem
            · exact Or.inr h
      · rw [if_neg mem, ih]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]

theorem length_le_insertAll (set xs : List BlockId) :
    set.length ≤ (insertAll set xs).length := by
  induction xs generalizing set with
  | nil => simp [insertAll]
  | cons y ys ih =>
      simp only [insertAll]
      by_cases mem : y ∈ set
      · rw [if_pos mem]
        exact ih set
      · rw [if_neg mem]
        have step := ih (set ++ [y])
        simp only [List.length_append, List.length_singleton] at step
        omega

theorem subset_of_length_insertAll_eq {set xs : List BlockId}
    (equal : (insertAll set xs).length = set.length) :
    ∀ x, x ∈ xs → x ∈ set := by
  induction xs generalizing set with
  | nil => intro x h; cases h
  | cons y ys ih =>
      intro x hx
      simp only [insertAll] at equal
      by_cases mem : y ∈ set
      · rw [if_pos mem] at equal
        rcases List.mem_cons.mp hx with rfl | hx
        · exact mem
        · exact ih equal x hx
      · rw [if_neg mem] at equal
        have step := length_le_insertAll (set ++ [y]) ys
        simp only [List.length_append, List.length_singleton] at step
        omega

theorem nodup_insertAll {set : List BlockId} (nodup : set.Nodup) (xs : List BlockId) :
    (insertAll set xs).Nodup := by
  induction xs generalizing set with
  | nil => simpa [insertAll] using nodup
  | cons y ys ih =>
      simp only [insertAll]
      by_cases mem : y ∈ set
      · rw [if_pos mem]
        exact ih nodup
      · rw [if_neg mem]
        apply ih
        apply List.nodup_append.mpr
        refine ⟨nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton.mp hb]
        intro equal
        exact mem (equal ▸ ha)

theorem insertAll_subset {U set xs : List BlockId}
    (setSub : set ⊆ U) (xsSub : xs ⊆ U) : insertAll set xs ⊆ U := by
  intro x hx
  rcases mem_insertAll.mp hx with h | h
  · exact setSub h
  · exact xsSub h

/-- One step of the closure: the non-`choose` successors of a set. -/
def expand (raw : RawFlow Ty) (set : List BlockId) : List BlockId :=
  set.flatMap raw.noChooseSuccessors

theorem expand_subset (raw : RawFlow Ty) (set : List BlockId) :
    raw.expand set ⊆ raw.allSuccessors := by
  intro x hx
  obtain ⟨y, _, hy⟩ := List.mem_flatMap.mp hx
  exact noChooseSuccessors_subset raw y hy

/-- Grow a set through its non-`choose` edges until it stops growing or the
fuel runs out. -/
def saturate (raw : RawFlow Ty) : Nat → List BlockId → List BlockId
  | 0, set => set
  | fuel + 1, set =>
    if (insertAll set (raw.expand set)).length = set.length then set
    else saturate raw fuel (insertAll set (raw.expand set))

theorem mem_saturate_of_mem (raw : RawFlow Ty) {x : BlockId} :
    ∀ (fuel : Nat) (set : List BlockId), x ∈ set → x ∈ raw.saturate fuel set := by
  intro fuel
  induction fuel with
  | zero => intro set h; simpa [saturate] using h
  | succ fuel ih =>
      intro set h
      simp only [saturate]
      split
      · exact h
      · exact ih _ (mem_insertAll.mpr (Or.inl h))

theorem saturate_sound (raw : RawFlow Ty) {start : BlockId} :
    ∀ (fuel : Nat) (set : List BlockId),
      (∀ x, x ∈ set → ReachableNoChoose raw start x) →
      ∀ x, x ∈ raw.saturate fuel set → ReachableNoChoose raw start x := by
  intro fuel
  induction fuel with
  | zero => intro set inv x hx; exact inv x (by simpa [saturate] using hx)
  | succ fuel ih =>
      intro set inv x hx
      simp only [saturate] at hx
      split at hx
      · exact inv x hx
      · apply ih _ _ x hx
        intro y hy
        rcases mem_insertAll.mp hy with hy | hy
        · exact inv y hy
        · obtain ⟨middle, middleMem, hy'⟩ := List.mem_flatMap.mp hy
          exact .step (inv middle middleMem) (mem_noChooseSuccessors.mp hy')

theorem saturate_closed_or_grows (raw : RawFlow Ty) :
    ∀ (fuel : Nat) (set : List BlockId),
      (∀ y, y ∈ raw.expand (raw.saturate fuel set) → y ∈ raw.saturate fuel set) ∨
        set.length + fuel ≤ (raw.saturate fuel set).length := by
  intro fuel
  induction fuel with
  | zero => intro set; right; simp [saturate]
  | succ fuel ih =>
      intro set
      simp only [saturate]
      by_cases stop : (insertAll set (raw.expand set)).length = set.length
      · rw [if_pos stop]
        left
        intro y hy
        exact subset_of_length_insertAll_eq stop y hy
      · rw [if_neg stop]
        rcases ih (insertAll set (raw.expand set)) with closed | grows
        · left; exact closed
        · right
          have grew : set.length + 1 ≤ (insertAll set (raw.expand set)).length :=
            Nat.lt_of_le_of_ne (length_le_insertAll _ _) (Ne.symm stop)
          omega

theorem nodup_saturate (raw : RawFlow Ty) :
    ∀ (fuel : Nat) {set : List BlockId}, set.Nodup → (raw.saturate fuel set).Nodup := by
  intro fuel
  induction fuel with
  | zero => intro set h; simpa [saturate] using h
  | succ fuel ih =>
      intro set h
      simp only [saturate]
      split
      · exact h
      · exact ih (nodup_insertAll h _)

theorem saturate_subset (raw : RawFlow Ty) {U : List BlockId}
    (succSub : raw.allSuccessors ⊆ U) :
    ∀ (fuel : Nat) {set : List BlockId}, set ⊆ U → raw.saturate fuel set ⊆ U := by
  intro fuel
  induction fuel with
  | zero => intro set h; simpa [saturate] using h
  | succ fuel ih =>
      intro set h
      simp only [saturate]
      split
      · exact h
      · exact ih (insertAll_subset h (fun x hx => succSub (expand_subset raw set hx)))

/-- A set closed under non-`choose` edges and containing `start` contains
everything `start` reaches. -/
theorem mem_of_closed (raw : RawFlow Ty) {S : List BlockId}
    (closed : ∀ y, y ∈ raw.expand S → y ∈ S) {start x : BlockId}
    (startMem : start ∈ S) (reach : ReachableNoChoose raw start x) : x ∈ S := by
  induction reach with
  | refl => exact startMem
  | step _ edge ih =>
      exact closed _ (List.mem_flatMap.mpr ⟨_, ih, mem_noChooseSuccessors.mpr edge⟩)

/-- Removing every copy of a present element shortens a list. Stated here, by
induction, to stay within the axiom ceiling. -/
private theorem length_filter_ne {a : BlockId} :
    ∀ {l : List BlockId}, a ∈ l →
      (l.filter fun x => decide (x ≠ a)).length + 1 ≤ l.length
  | [], mem => absurd mem List.not_mem_nil
  | b :: bs, mem => by
      by_cases eq : b = a
      · subst eq
        rw [List.filter_cons_of_neg (p := fun x => decide (x ≠ b))
          (by rw [decide_eq_false (fun h => h rfl)]; exact Bool.false_ne_true)]
        rw [List.length_cons]
        exact Nat.succ_le_succ (List.length_filter_le _ _)
      · rw [List.filter_cons_of_pos (p := fun x => decide (x ≠ a)) (decide_eq_true eq),
          List.length_cons, List.length_cons]
        have tailMem : a ∈ bs := by
          rcases List.mem_cons.mp mem with h | h
          · exact absurd h.symm eq
          · exact h
        have ih := length_filter_ne tailMem
        omega

/-- A duplicate-free list is no longer than any list containing it. -/
private theorem length_le_of_nodup_subset :
    ∀ {l₁ l₂ : List BlockId}, l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, l₂, nodup, sub => by
      have ⟨notMem, nodupTail⟩ := List.nodup_cons.mp nodup
      have aMem : a ∈ l₂ := sub List.mem_cons_self
      have tailSub : l ⊆ l₂.filter fun x => decide (x ≠ a) := by
        intro x hx
        have ne : x ≠ a := fun eq => notMem (eq ▸ hx)
        exact List.mem_filter.mpr ⟨sub (List.mem_cons_of_mem _ hx), decide_eq_true ne⟩
      have ih := length_le_of_nodup_subset nodupTail tailSub
      have bound := length_filter_ne aMem
      rw [List.length_cons]
      omega

/-- The blocks reachable from `start` through non-`choose` edges. -/
def reachSet (raw : RawFlow Ty) (start : BlockId) : List BlockId :=
  raw.saturate (raw.allSuccessors.length + 2) [start]

theorem mem_reachSet {raw : RawFlow Ty} {start x : BlockId} :
    x ∈ raw.reachSet start ↔ ReachableNoChoose raw start x := by
  constructor
  · intro mem
    exact saturate_sound raw _ [start]
      (fun y hy => by rw [List.mem_singleton.mp hy]; exact .refl _) x mem
  · intro reach
    rcases saturate_closed_or_grows raw (raw.allSuccessors.length + 2) [start] with closed | grows
    · exact mem_of_closed raw closed (mem_saturate_of_mem raw _ _ (List.mem_singleton_self start)) reach
    · exfalso
      have bounded : (raw.reachSet start).length ≤ (start :: raw.allSuccessors).length :=
        length_le_of_nodup_subset
          (nodup_saturate raw _ (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩))
          (saturate_subset raw (fun y hy => List.mem_cons_of_mem _ hy) _
            (fun y hy => by rw [List.mem_singleton.mp hy]; exact List.mem_cons_self))
      simp only [reachSet] at bounded
      simp only [List.length_cons] at grows bounded
      omega

end RawFlow

/-- Decidable checker for `CyclesWF`: no declared non-`choose` block reaches
itself through non-`choose` edges starting from one of its successors. Needs
no `DecidableEq Ty`. -/
def cyclesChoose (raw : RawFlow Ty) : Bool :=
  raw.blocks.all fun block =>
    block.term.isChoose ||
      block.term.successors.all fun next => !decide (block.id ∈ raw.reachSet next)

theorem cyclesChoose_iff {raw : RawFlow Ty} :
    cyclesChoose raw = true ↔ CyclesWF raw := by
  constructor
  · intro checked source target edge reach
    obtain ⟨block, mem, idEq, notChoose, targetMem⟩ := edge
    have blockOk := List.all_eq_true.mp checked block mem
    rw [notChoose, Bool.false_or] at blockOk
    have nextOk := List.all_eq_true.mp blockOk target targetMem
    have inSet : block.id ∈ raw.reachSet target := by
      rw [idEq]
      exact RawFlow.mem_reachSet.mpr reach
    rw [decide_eq_true inSet] at nextOk
    exact Bool.false_ne_true nextOk
  · intro wf
    apply List.all_eq_true.mpr
    intro block mem
    cases chooseEq : block.term.isChoose with
    | true => rfl
    | false =>
      rw [Bool.false_or]
      apply List.all_eq_true.mpr
      intro next nextMem
      have notMem : block.id ∉ raw.reachSet next := fun inSet =>
        wf block.id next ⟨block, mem, rfl, chooseEq, nextMem⟩ (RawFlow.mem_reachSet.mp inSet)
      rw [decide_eq_false notMem]
      rfl

end Effects
