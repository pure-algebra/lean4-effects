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
deriving DecidableEq, Repr

namespace RawTerm

/-- Direct graph successors named by a raw terminator, in source order. -/
def successors : RawTerm → List BlockId
  | .ret _ => []
  | .jump target _ => [target]
  | .perform _ _ target _ => [target]
  | .choose _ left right _ => [left, right]

/-- The argument list every successor receives. -/
def args : RawTerm → List Var
  | .ret _ => []
  | .jump _ args => args
  | .perform _ _ _ args => args
  | .choose _ _ _ args => args

/-- Every variable occurrence in source order; a `perform` names its request
before its arguments. -/
def operands : RawTerm → List Var
  | .ret value => [value]
  | .jump _ args => args
  | .perform _ request _ args => request :: args
  | .choose _ _ _ args => args

/-- The number of values every successor receives; a `perform` adds the answer. -/
def arity : RawTerm → Nat
  | .ret _ => 0
  | .jump _ args => args.length
  | .perform _ _ _ args => args.length + 1
  | .choose _ _ _ args => args.length

/-- Only `choose` is a decision. -/
def isChoose : RawTerm → Bool
  | .choose .. => true
  | _ => false

/-- The decision of a `choose`. -/
def decision? : RawTerm → Option DecisionId
  | .choose decision _ _ _ => some decision
  | _ => none

end RawTerm

/-- A first-order block: identity, parameter types, terminator. -/
structure RawBlock (Ty : Type uTy) where
  id : BlockId
  params : List Ty
  term : RawTerm
deriving DecidableEq, Repr

end Effects
