import Std

/-!
# First-order flow blocks

This module owns the nominal identities, closed operation alphabet, and raw
block terms used by flow admission. Raw terms contain only stable identities
and parameter positions; they deliberately contain no Lean continuation or
semantic `Program`.

Flow v2 (`test/contracts/flow-v2.contract.md`): every block has a parameter
list, a terminator names its operands by position in that list, `jump` and
`choose` pass an argument list, and `perform` passes an argument list plus
the operation's answer.

Flow v3 (`test/contracts/flow-v3.contract.md`, which supersedes v2's
terminator list) adds two terminators and makes the two edge clauses
successor-indexed.

* `performCatch` is a `perform` with a failure successor. Its two edges carry
  *different* argument lists and *different* arities, which is why `argsAt`
  and `arityAt` below are keyed by the position of the edge in `successors`
  rather than by the terminator alone. `args` and `arity` stay the value
  edge's, so every v2 shape reads exactly as it did.
* `branch` is taken by the *value* of its test operand and is still a decision
  *site*: `isChoose` is true for it, so `CyclesWF` counts it and a finite tape
  still bounds every run. The test operand carries the alphabet's boolean
  spelling (`FlowAlphabet.boolTy`).
-/

namespace Effects

/-- Stable identity of a declared flow block. -/
structure BlockId where
  value : Nat
deriving DecidableEq, Repr

/-- Stable identity of an operation in a closed flow alphabet. -/
structure OperationId where
  value : Nat
deriving DecidableEq, Repr

/-- Stable identity of the closed alphabet expected by a raw flow. -/
structure AlphabetId where
  value : Nat
deriving DecidableEq, Repr

/-- Stable identity of an explicit nondeterministic decision site. -/
structure DecisionId where
  value : Nat
deriving DecidableEq, Repr

/-- A position in the current block's parameter list. It is not a name, has no
scope beyond its block, and is typed by `params[index]`. -/
structure Var where
  index : Nat
deriving DecidableEq, Repr

/--
A closed operation alphabet supplied at the admission boundary.

Raw flows retain only `id`. Executable lookup and its two inverse laws remain
in this trusted semantic environment, so no host function enters canonical
flow content.
-/
structure FlowAlphabet.{uTy, uOp} (Ty : Type uTy) where
  id : AlphabetId
  Op : Type uOp
  operationId : Op → OperationId
  lookup : OperationId → Option Op
  requestTy : Op → Ty
  answerTy : Op → Ty
  /-- The declared error type of an operation (Flow v3): the type of the value
  a `performCatch` binds in the last slot of its failure successor, and `none`
  for an operation that cannot fail.

  v0.8.0 made this an `Option`. It used to be a total `Op → Ty`, and the
  comment here asked an operation that cannot fail to "declare the alphabet's
  own empty spelling" — a convention the type could not express, since `Ty` is
  a code type with no emptiness predicate, and one an alphabet could satisfy
  by declaring `errorTy op = answerTy op`. `performCatch` admission was
  therefore weaker than it read. `none` makes "cannot fail" a fact of the
  table, decidable without any predicate on `Ty`, and the admission clause
  `catchUnfailable` refuses a `performCatch` on such an operation. The
  boundary still never reads a spelling, it only compares. -/
  errorTy : Op → Option Ty
  /-- The spelling a `branch` test operand must carry (Flow v3). -/
  boolTy : Ty
  lookup_operationId : ∀ operation,
    lookup (operationId operation) = some operation
  operationId_of_lookup : ∀ {id operation},
    lookup id = some operation → operationId operation = id

/-- A first-order block terminator. Every continuation is a nominal block ID
with an argument list; every operand is a parameter position. -/
inductive RawTerm where
  | ret (value : Var)
  | jump (target : BlockId) (args : List Var)
  /-- The target receives `args ++ [answer]`. -/
  | perform (operation : OperationId) (request : Var) (target : BlockId) (args : List Var)
  /-- Both targets receive `args`. -/
  | choose (decision : DecisionId) (left right : BlockId) (args : List Var)
  /-- A `perform` with a failure successor (Flow v3). On `.ok answer` the value
  successor `target` receives `args ++ [answer]`; on `.error e` the failure
  successor `onError` receives `errorArgs ++ [e]`, where `e` carries the
  operation's declared error type. The two edges therefore have different
  argument lists and different arities. -/
  | performCatch (operation : OperationId) (request : Var) (target : BlockId)
      (args : List Var) (onError : BlockId) (errorArgs : List Var)
  /-- A branch taken by the *value* of `test` at decision site `site` (Flow
  v3). Both targets receive `args`. It is a value test and a decision site at
  once: a run reads the tape entry at `site` exactly as a `choose` does and
  refuses when the tape disagrees with the value, so the tape bound and
  `CyclesWF` are unchanged. -/
  | branch (test : Var) (site : DecisionId) (onTrue onFalse : BlockId) (args : List Var)
deriving DecidableEq, Repr

namespace RawTerm

/-- Direct graph successors named by a raw terminator, in source order. -/
def successors : RawTerm → List BlockId
  | .ret _ => []
  | .jump target _ => [target]
  | .perform _ _ target _ => [target]
  | .choose _ left right _ => [left, right]
  | .performCatch _ _ target _ onError _ => [target, onError]
  | .branch _ _ onTrue onFalse _ => [onTrue, onFalse]

/-- The argument list the *value* successor receives. A `performCatch`'s
failure successor takes `argsAt` at edge `1`. -/
def args : RawTerm → List Var
  | .ret _ => []
  | .jump _ args => args
  | .perform _ _ _ args => args
  | .choose _ _ _ args => args
  | .performCatch _ _ _ args _ _ => args
  | .branch _ _ _ _ args => args

/-- The argument list the successor at position `edge` of `successors`
receives. Only `performCatch` distinguishes its edges. -/
def argsAt : RawTerm → Nat → List Var
  | .performCatch _ _ _ args _ errorArgs, edge => if edge = 1 then errorArgs else args
  | term, _ => term.args

/-- Every variable occurrence in source order; a `perform` names its request
before its arguments, a `performCatch` its request before both lists, and a
`branch` its test before its arguments. -/
def operands : RawTerm → List Var
  | .ret value => [value]
  | .jump _ args => args
  | .perform _ request _ args => request :: args
  | .choose _ _ _ args => args
  | .performCatch _ request _ args _ errorArgs => request :: (args ++ errorArgs)
  | .branch test _ _ _ args => test :: args

/-- The number of values the *value* successor receives; a `perform` adds the
answer. A `performCatch`'s failure successor takes `arityAt` at edge `1`. -/
def arity : RawTerm → Nat
  | .ret _ => 0
  | .jump _ args => args.length
  | .perform _ _ _ args => args.length + 1
  | .choose _ _ _ args => args.length
  | .performCatch _ _ _ args _ _ => args.length + 1
  | .branch _ _ _ _ args => args.length

/-- The number of values the successor at position `edge` of `successors`
receives. Only `performCatch` distinguishes its edges: its failure successor
receives `errorArgs ++ [error]`. -/
def arityAt : RawTerm → Nat → Nat
  | .performCatch _ _ _ args _ errorArgs, edge =>
      if edge = 1 then errorArgs.length + 1 else args.length + 1
  | term, _ => term.arity

/-- A decision site: `choose`, and `branch`, whose value test is read from the
tape as well. -/
def isChoose : RawTerm → Bool
  | .choose .. => true
  | .branch .. => true
  | _ => false

/-- The decision site of a `choose` or a `branch`. -/
def decision? : RawTerm → Option DecisionId
  | .choose decision _ _ _ => some decision
  | .branch _ site _ _ _ => some site
  | _ => none

/-- The alphabet operation a terminator performs, if it performs one. -/
def operation? : RawTerm → Option OperationId
  | .perform operation _ _ _ => some operation
  | .performCatch operation _ _ _ _ _ => some operation
  | _ => none

/-- The request operand of a terminator that performs an operation. -/
def request? : RawTerm → Option Var
  | .perform _ request _ _ => some request
  | .performCatch _ request _ _ _ _ => some request
  | _ => none

@[simp] theorem argsAt_ret (value : Var) (edge : Nat) :
    (RawTerm.ret value).argsAt edge = [] := rfl

@[simp] theorem argsAt_jump (target : BlockId) (args : List Var) (edge : Nat) :
    (RawTerm.jump target args).argsAt edge = args := rfl

@[simp] theorem argsAt_perform (operation : OperationId) (request : Var) (target : BlockId)
    (args : List Var) (edge : Nat) :
    (RawTerm.perform operation request target args).argsAt edge = args := rfl

@[simp] theorem argsAt_choose (decision : DecisionId) (left right : BlockId)
    (args : List Var) (edge : Nat) :
    (RawTerm.choose decision left right args).argsAt edge = args := rfl

@[simp] theorem argsAt_branch (test : Var) (site : DecisionId) (onTrue onFalse : BlockId)
    (args : List Var) (edge : Nat) :
    (RawTerm.branch test site onTrue onFalse args).argsAt edge = args := rfl

@[simp] theorem argsAt_performCatch (operation : OperationId) (request : Var)
    (target : BlockId) (args : List Var) (onError : BlockId) (errorArgs : List Var)
    (edge : Nat) :
    (RawTerm.performCatch operation request target args onError errorArgs).argsAt edge =
      if edge = 1 then errorArgs else args := rfl

@[simp] theorem arityAt_ret (value : Var) (edge : Nat) :
    (RawTerm.ret value).arityAt edge = 0 := rfl

@[simp] theorem arityAt_jump (target : BlockId) (args : List Var) (edge : Nat) :
    (RawTerm.jump target args).arityAt edge = args.length := rfl

@[simp] theorem arityAt_perform (operation : OperationId) (request : Var) (target : BlockId)
    (args : List Var) (edge : Nat) :
    (RawTerm.perform operation request target args).arityAt edge = args.length + 1 := rfl

@[simp] theorem arityAt_choose (decision : DecisionId) (left right : BlockId)
    (args : List Var) (edge : Nat) :
    (RawTerm.choose decision left right args).arityAt edge = args.length := rfl

@[simp] theorem arityAt_branch (test : Var) (site : DecisionId) (onTrue onFalse : BlockId)
    (args : List Var) (edge : Nat) :
    (RawTerm.branch test site onTrue onFalse args).arityAt edge = args.length := rfl

@[simp] theorem arityAt_performCatch (operation : OperationId) (request : Var)
    (target : BlockId) (args : List Var) (onError : BlockId) (errorArgs : List Var)
    (edge : Nat) :
    (RawTerm.performCatch operation request target args onError errorArgs).arityAt edge =
      if edge = 1 then errorArgs.length + 1 else args.length + 1 := rfl

theorem argsAt_zero (term : RawTerm) : term.argsAt 0 = term.args := by
  cases term <;> simp [args]

theorem arityAt_zero (term : RawTerm) : term.arityAt 0 = term.arity := by
  cases term <;> simp [arity]

/-- Off the failure edge every terminator supplies its value list. -/
theorem argsAt_of_ne_one {term : RawTerm} {edge : Nat} (ne : edge ≠ 1) :
    term.argsAt edge = term.args := by
  cases term <;> simp [args, ne]

theorem arityAt_of_ne_one {term : RawTerm} {edge : Nat} (ne : edge ≠ 1) :
    term.arityAt edge = term.arity := by
  cases term <;> simp [arity, ne]

end RawTerm

/-- A first-order block: identity, parameter types, terminator. -/
structure RawBlock (Ty : Type uTy) where
  id : BlockId
  params : List Ty
  term : RawTerm
deriving DecidableEq, Repr

end Effects
