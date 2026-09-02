import Effects.Algebra.Handler

/-!
# Named-operation families and the first-order alphabet embedding

A `Family` is what a service class is: a name, a parameter type and an answer
type per name. Its signature is the Σ-type of name and parameter. A `Service`
record is one method per name and is the same thing as a handler for that
signature. An `Alphabet` is the first-order table (names with type codes);
a denotation of the codes embeds it as a family. The embeddings are `abbrev`
so that instance synthesis sees through them.
-/

namespace Effects

universe uOp uAns uS uT uU uN uP uTarget


set_option linter.checkUnivs false in
/-- The shape a service class has: names, a parameter type and an answer type
per name. This is what a DSL emits and what `Context.Service` renders from. -/
structure Family.{n, p, a} where
  Name : Type n
  Param : Name → Type p
  Answer : Name → Type a

namespace Family

/-- The semantic signature: an operation is a name applied to a parameter. -/
abbrev toSignature (F : Family.{uN, uP, uAns}) : Signature.{max uN uP, uAns} :=
  ⟨Σ name, F.Param name, fun operation => F.Answer operation.1⟩

def perform (F : Family.{uN, uP, uAns}) (name : F.Name) (param : F.Param name) :
    Program F.toSignature (F.Answer name) :=
  Program.perform (S := F.toSignature) ⟨name, param⟩

/-- A service record: one method per name. Exactly the object a
`Context.Service` class carries, and exactly a curried handler. -/
def Service (F : Family.{uN, uP, uAns}) (M : Type uAns → Type uTarget) : Type _ :=
  ∀ name, F.Param name → M (F.Answer name)

def Service.toHandler {F : Family.{uN, uP, uAns}} {M : Type uAns → Type uTarget}
    (service : F.Service M) : Handler F.toSignature M :=
  ⟨fun operation => service operation.1 operation.2⟩

def Service.ofHandler {F : Family.{uN, uP, uAns}} {M : Type uAns → Type uTarget}
    (handler : Handler F.toSignature M) : F.Service M :=
  fun name param => handler.handle ⟨name, param⟩

theorem Service.toHandler_ofHandler {F : Family.{uN, uP, uAns}} {M : Type uAns → Type uTarget}
    (handler : Handler F.toSignature M) : (Service.ofHandler handler).toHandler = handler :=
  Handler.ext fun ⟨_, _⟩ => rfl

theorem Service.ofHandler_toHandler {F : Family.{uN, uP, uAns}} {M : Type uAns → Type uTarget}
    (service : F.Service M) : Service.ofHandler service.toHandler = service := by
  funext name param
  rfl

end Family

/-- The first-order alphabet: Effect4's `FlowAlphabet` minus its identity
fields. `Ty` is a code type; nothing here is a Lean `Type`. -/
structure Alphabet.{t, o} (Ty : Type t) where
  Op : Type o
  requestTy : Op → Ty
  answerTy : Op → Ty

/-- The embedding: a denotation of codes turns an alphabet into a family, and
therefore into a signature. This is the "first-order carrier with its own
embedding theorem" the claim boundary promises downstream. -/
abbrev Alphabet.toFamily {Ty : Type uT} (alphabet : Alphabet.{uT, uOp} Ty)
    (denote : Ty → Type uAns) : Family.{uOp, uAns, uAns} :=
  ⟨alphabet.Op, fun o => denote (alphabet.requestTy o), fun o => denote (alphabet.answerTy o)⟩

end Effects
