import Lean
import Lean.Util.CollectAxioms
import Effects

/-!
# Effects axiom allowlist gate

This command tokenizes every authored `Effects` source and inspects every
declaration compiled from it, including definitions, instances, generated
declarations, and private helper declarations. The build fails on an authored
trust token, on a bodyless `opaque`, or if any declaration reaches an axiom
outside the library's current ceiling: propositional extensionality and
quotient soundness.

The gate is intentionally exhaustive over the compiled namespace rather than
maintaining a hand-written theorem list. The separate axiom report remains a
human-readable receipt.

## Why the source is tokenized at all

The declaration pass reads `environment.constants`, and Lean's `example` never
enters the environment (`Lean/Elab/MutualDef.lean`: `if isExample views then
withoutModifyingEnv do`). Every trust token written inside an `example` is
therefore invisible to it — including `sorry`, which is a warning rather than
an error and leaves the build green. The source pass is what closes that hole:
it visits every token of every audited file whether or not the surrounding
declaration is named. `forbiddenTrustTokens` records what it refuses and why.

## Bodyless `opaque`

`opaque f : T` with no body is refused. Lean synthesises
`default_or_ofNonempty%` for the missing value (`Lean/Elab/DefView.lean`), so
the constant denotes an arbitrary inhabitant nobody chose: an uninterpreted
symbol wearing a definition's clothes, and every receipt stated about it is a
receipt about nothing. The refusal is a declaration-level check rather than a
token, because the source tokenizer sees the `opaque` keyword but cannot see
whether a `:=` follows it. The two shapes are told apart by the synthesised
value's head constant, which is `Inhabited.default` or `Classical.ofNonempty`
and nothing else.

## Provenance

Kept in step with lean4-effect4's `Effect4Test/Audit/AxiomGate.lean` at
`fd40762`. Survey finding #46: the two gates had drifted, each holding a check
the other lacked. This file gains that gate's token list, its `opaque` refusal
and its reserved-name ancestor rule; that gate gains this one's missing
-directory guard (`leanSources`), which is what lets `Effects/` be absent
between split slices.
-/

open Lean

namespace EffectsTest.Audit

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound]

private def auditImplementationAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

/--
Modules whose declarations are audit *implementation* — metaprogramming that
inspects the environment — rather than semantic or test content.

`Classical.choice` is unavoidable in `MetaM`, so these modules are bound by
`auditImplementationAxioms` instead of `allowedAxioms`. The list is explicit
rather than a namespace prefix on purpose: a prefix would let any file dropped
into the audit tree silently acquire `Classical.choice`, which is the trust
boundary this gate exists to hold.

The list is checked for staleness below. A module named here that no longer
needs the exemption fails the gate, so an entry cannot outlive its reason.
-/
private def auditImplementationModules : List Name :=
  [ `EffectsTest.Audit.AxiomGate ]

private def targetImplementationModules : List Name := []

private def choiceImplementationModules : List Name :=
  auditImplementationModules ++ targetImplementationModules

/-- Exact declaration-level `Classical.choice` admissions. Empty: `Effects`
has no rendering or string-traversal implementation. An entry added here
needs an authored admission in `docs/CLAIM-BOUNDARY.md`. -/
private def choiceImplementationDeclarations : List Name := []

/-- Private rendering helpers are identified by exact owner and original name,
never a namespace prefix or Lean's unstable private-name counter. -/
private def choiceImplementationPrivateDeclarations : List (Name × Name) := []

private def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/--
The authored trust tokens the source gate refuses, in either shape Lean's
tokenizer can produce for them.

Which shape a word takes depends on the token table of the environment doing
the audit, and the two halves do not agree at this pin: `unsafe`, `partial`,
`sorry` and `axiom` are keywords and arrive as atoms, while `native_decide`,
`extern` and `implemented_by` are ordinary identifiers. Checking both shapes
means the list states a policy rather than tracking Lean's grammar.

What each one buys:

* `unsafe`, `partial` — the original two; the compiled-environment pass below
  independently confirms `isUnsafe`/`isPartial`, and this catches them inside
  an `example`, where there is no constant to inspect.
* `sorry` — an admitted goal is a warning, not an error, so a `sorry` inside an
  `example` leaves no constant, emits no failure, and keeps the build green.
  Outside an `example` it also reaches `sorryAx`, which `forbiddenAxioms`
  refuses; this is the half that has no declaration behind it.
* `axiom` — a new axiom is only visible to the axiom pass once something
  reaches it. The gate's ceiling is a claim about what the tree *contains*, so
  the declaration is refused where it is written.
* `native_decide` — closes the goal by compiler evaluation and reaches
  `Lean.ofReduceBool`, already in `forbiddenAxioms`; again the point is the
  `example` that leaves nothing to inspect.
* `extern`, `implemented_by` — replace a checked Lean body with host code at
  runtime. Neither moves an axiom, and neither is a claim this tree is entitled
  to make about its own semantics.

An identifier is judged by its *raw* source text, never by its resolved name,
so the escaped `«unsafe»` of `test/fixtures/trust-gate/benign.lean.txt` stays a
name and a string literal stays prose.
-/
private def forbiddenTrustTokens : List String :=
  [ "unsafe", "partial", "sorry", "axiom"
  , "native_decide", "extern", "implemented_by" ]

/--
`admit` is refused only as a keyword.

At this toolchain pin it is not one: the tactic does not exist, so `admit`
tokenizes as an identifier — and it is the name of `Effects.admit`, this
package's own flow-admission function. Refusing the identifier would refuse
`Effects/Flow/{Admission,Checked,Region}.lean` and every battery that calls it,
so the entry sits here and fires only if a future toolchain reintroduces the
tactic and puts the word in the token table. Nothing is lost meanwhile: the
tactic expands to `sorry`, which the list above refuses, and reaches `sorryAx`,
which `forbiddenAxioms` refuses.
-/
private def forbiddenTrustKeywords : List String :=
  [ "admit" ]

/-- The synthesised values Lean gives a bodyless `opaque`. -/
private def synthesizedOpaqueBodies : List Name :=
  [``Inhabited.default, ``Classical.ofNonempty]

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

private def resolveChoiceImplementationDeclarations
    (environment : Environment) (declarations : Array Name) : Except String (List Name) := do
  let mut resolved := choiceImplementationDeclarations
  for (owner, originalName) in choiceImplementationPrivateDeclarations do
    let privateCandidates := declarations.toList.filter fun declaration =>
      moduleOf? environment declaration == some owner &&
        privateToUserName? declaration == some originalName
    match privateCandidates with
    | [declaration] => resolved := resolved ++ [declaration]
    | _ => throw s!"Effects axiom gate: private implementation exemption {owner}/{originalName} matched {privateCandidates.length} declarations; expected exactly one"
  return resolved

/-- The ancestors reachable by walking up while the parent stays in the same
module as the declaration. A definition's `match_<n>`, `proof_<n>` and private
helpers land beside it, under its own author's control, so they are judged by
it. The walk stops at the first parent that lives elsewhere. -/
private def sameModuleAncestors
    (environment : Environment) (declarationModule : Option Name) : Name → List Name
  | .anonymous => []
  | .str parent _ =>
      if moduleOf? environment parent == declarationModule then
        parent :: sameModuleAncestors environment declarationModule parent
      else []
  | .num parent _ =>
      if moduleOf? environment parent == declarationModule then
        parent :: sameModuleAncestors environment declarationModule parent
      else []

/--
The ancestors whose admission a declaration may inherit. Two shapes, and
nothing else.

* A parent in the *same module*, per `sameModuleAncestors`.
* The immediate parent of a name Lean itself *reserves* for it. An equation
  lemma is minted in whichever module first unfolds `f`, so `f.eq_def` and
  `f.eq_<n>` genuinely live somewhere else, and this is the only way admission
  crosses a module boundary.

The second clause reads `Lean.isReservedName` rather than the spelling, and
that distinction is the whole of it: a foreign module can declare
`f.proof_1`, `f.match_1` and `f._spec_1` — ordinary names Lean reserves nothing
about — while `f.eq_1` is refused outright. A suffix-spelling test would have
handed the admission to any of the first three.

`Effects`' exemption list is one module today, so nothing here is load-bearing
yet; it exists so that the first real declaration-level admission does not
also have to reason about its generated auxiliaries. Without any cross-module
clause, a gate that admits anything at all refuses that thing's own equation
lemmas the moment another module unfolds it.
-/
private def admissionAncestors (environment : Environment) (declaration : Name) : List Name :=
  let sameModule :=
    sameModuleAncestors environment (moduleOf? environment declaration) declaration
  if Lean.isReservedName environment declaration then
    declaration.getPrefix :: sameModule
  else
    sameModule

/-- Strip the binders a parameterised `opaque` puts in front of its value.
`opaque f (n : Nat) : Nat` has value `fun n => default`, and the head constant
is what the ruling reads. The bound is generous; no authored signature in this
tree approaches it. -/
private def stripBinders : Nat → Expr → Expr
  | 0, value => value
  | fuel + 1, value =>
      if value.isLambda then stripBinders fuel value.bindingBody! else value

/-- Whether an `opaque` declaration's value is the one Lean synthesised for a
missing body rather than one an author wrote. See the ruling in the module
header. -/
private def isSynthesizedOpaqueBody (value : Expr) : Bool :=
  match (stripBinders 64 value).getAppFn with
  | .const name _ => synthesizedOpaqueBodies.contains name
  | _ => false

private def belongsToAuditedTree (moduleName : Name) : Bool :=
  (`Effects).isPrefixOf moduleName || (`EffectsTest).isPrefixOf moduleName

private def isGeneratedSafeRecursor (environment : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match environment.find? sourceName with
      | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
      | none => false
      | _ => false

/-
`Parser.testParseFile` cannot replay an already-compiled source against the
final project environment: syntax introduced by a later-imported test module
can turn an earlier ordinary identifier into a keyword. Tokenization is the
right level for this source check. Lean's own tokenizer skips comments and
handles ordinary, character, interpolated, and raw string literals, while the
compiled-environment pass below independently confirms declaration safety.
-/
/-- The forbidden word a single token carries, if any. A keyword arrives as an
atom whose value is the word; an ordinary identifier arrives as an ident, and
is judged by the raw source text so that `«unsafe»` and `Foo.unsafe` are names
rather than modifiers. Every other token shape — string, char, and numeric
literals above all — carries none. -/
private def forbiddenToken? (token : Syntax) : Option String :=
  match token with
  | .atom _ value =>
      let value := value.trimAscii.toString
      if forbiddenTrustTokens.contains value || forbiddenTrustKeywords.contains value then
        some value
      else
        none
  | .ident _ rawValue _ _ =>
      let raw := rawValue.toString
      if forbiddenTrustTokens.contains raw then some raw else none
  | _ => none

private def forbiddenTrustToken?
    (environment : Environment)
    (source : System.FilePath) : IO (Option String) := do
  let input ← IO.FS.readFile source
  let inputContext := Parser.mkInputContext input source.toString
  let parserContext : Parser.ParserModuleContext :=
    { env := environment, options := {} }
  let tokenTable := Parser.Module.updateTokens (Parser.getTokenTable environment)
  let mut state := Parser.mkParserState input
  let mut projectionEnd : Option String.Pos.Raw := none
  while !inputContext.atEnd state.pos do
    let skipped := Parser.whitespace.run inputContext parserContext tokenTable state
    if let some error := skipped.errorMsg then
      throw <| IO.userError
        s!"Effects source trust gate: tokenization failed in {source}: {error}"
    state := skipped
    if inputContext.atEnd state.pos then
      return none
    -- Documentation comments are syntax nodes rather than whitespace. Consume
    -- them with Lean's own parsers so their prose never becomes audit tokens.
    let docComment := Parser.Command.docComment.fn.run
      inputContext parserContext tokenTable state
    if docComment.errorMsg.isNone then
      state := docComment.popSyntax
      projectionEnd := none
      continue
    let moduleDoc := Parser.Command.moduleDoc.fn.run
      inputContext parserContext tokenTable state
    if moduleDoc.errorMsg.isNone then
      state := moduleDoc.popSyntax
      projectionEnd := none
      continue
    -- Lean parses the index in `h.2.trans` and `h |>.2.trans` with
    -- `fieldIdxFn`: the ordinary number tokenizer mistakes `2.trans` for a
    -- decimal. Use the same parser only immediately after a projection dot;
    -- ordinary numerals and every tokenization error retain their usual path.
    let tokenParser :=
      if projectionEnd == some state.pos && (inputContext.get state.pos).isDigit then
        Parser.fieldIdxFn
      else
        Parser.tokenFn []
    let next := tokenParser.run inputContext parserContext tokenTable state
    if let some error := next.errorMsg then
      let position := inputContext.fileMap.toPosition state.pos
      throw <| IO.userError
        s!"Effects source trust gate: tokenization failed in {source}:{position.line}:{position.column + 1}: {error}"
    let token := next.stxStack.back
    if let some found := forbiddenToken? token then
      return some found
    projectionEnd :=
      if token.isToken "." || token.isToken "|>." then token.getTailPos? else none
    state := next.popSyntax
  return none

private def auditSourceTrustModifiers
    (environment : Environment)
    (sources : Array System.FilePath) : IO Unit := do
  for source in sources do
    if let some token ← forbiddenTrustToken? environment source then
      throw <| IO.userError
        s!"Effects source trust gate: {source} contains an authored `{token}` trust token"

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "Effects.lean").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "Effects axiom gate: could not locate the project root"
  throw <| IO.userError "Effects axiom gate: project-root search exceeded 64 parents"

/-- Every `.lean` file under `directory`, or none when the tree does not exist
yet (the production tree is absent between slices S1 and S2). -/
private def leanSources (directory : System.FilePath) : IO (Array System.FilePath) := do
  if !(← directory.pathExists) then
    return #[]
  let files ← directory.walkDir
  return files.filter fun path => path.extension == some "lean"

private def auditedSources (projectRoot : System.FilePath) : IO (Array System.FilePath) := do
  let library ← leanSources (projectRoot / "Effects")
  let tests ← leanSources (projectRoot / "EffectsTest")
  return library ++ tests |>.push (projectRoot / "Effects.lean")
    |>.push (projectRoot / "EffectsTest.lean")

open Lean Elab Command in
elab "#effects_axiom_gate" : command => do
  let environment ← getEnv
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "Effects axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let sources ← liftIO <| auditedSources projectRoot
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    (Lean.modToFilePath projectRoot moduleName "lean").normalize
  for source in sources do
    if source.normalize != sourceFile.normalize && !importedPaths.contains source.normalize then
      throwError
        "Effects module-closure gate: {source} is not reachable from the EffectsTest audit root"

  liftIO <| auditSourceTrustModifiers environment sources

  let mut declarations : Array Name := #[]
  for (name, info) in environment.constants.toList do
    if let some moduleName := moduleOf? environment name then
      if belongsToAuditedTree moduleName then
        if !isGeneratedSafeRecursor environment name then
          if info.isUnsafe then
            throwError "Effects trust gate: declaration {name} is unsafe"
          if info.isPartial then
            throwError "Effects trust gate: declaration {name} is partial"
          if let .opaqueInfo opaqueInfo := info then
            if isSynthesizedOpaqueBody opaqueInfo.value then
              throwError
                "Effects trust gate: declaration {name} is an `opaque` with no body, so it \
                 denotes an arbitrary inhabitant rather than the value it advertises; give it \
                 a body or make the boundary an authored admission"
        declarations := declarations.push name

  let exactImplementationDeclarations ←
    match resolveChoiceImplementationDeclarations environment declarations with
    | .ok resolved => pure resolved
    | .error message => throwError "{message}"

  let admitted (declaration : Name) : Bool :=
    (moduleOf? environment declaration).any choiceImplementationModules.contains ||
      exactImplementationDeclarations.contains declaration
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    -- An auxiliary or equation lemma inherits the admission of the declaration
    -- it was generated from; see `admissionAncestors` for which parents count.
    let bound :=
      if admitted declaration || (admissionAncestors environment declaration).any admitted then
        auditImplementationAxioms
      else
        allowedAxioms
    for axiomName in axioms do
      if forbiddenAxioms.contains axiomName then
        throwError
          "Effects axiom gate: declaration {declaration} reaches forbidden axiom {axiomName}"
      if !bound.contains axiomName then
        throwError
          "Effects axiom gate: declaration {declaration} reaches unexpected axiom {axiomName}; allowed axioms are {bound}"

  -- The exemption list must not outlive its reason. A named implementation
  -- module that no longer reaches `Classical.choice` is a stale entry and
  -- widens the trust boundary for nothing, so it fails the gate.
  for exempted in choiceImplementationModules do
    let mut used := false
    for declaration in declarations do
      if moduleOf? environment declaration == some exempted then
        if (← collectAxioms declaration).contains ``Classical.choice then
          used := true
    if !used then
      throwError
        "Effects axiom gate: stale implementation exemption for {exempted}; no declaration in it reaches Classical.choice, so remove it from choiceImplementationModules"

  for exempted in exactImplementationDeclarations do
    if !(declarations.contains exempted) then
      throwError
        "Effects axiom gate: exact implementation exemption names missing declaration {exempted}"
    if !(← collectAxioms exempted).contains ``Classical.choice then
      throwError
        "Effects axiom gate: stale exact implementation exemption for {exempted}; it no longer reaches Classical.choice"

  logInfo
    m!"Effects module and axiom gate: checked {sources.size} modules and {declarations.size} declarations; semantic/test axioms are {allowedAxioms}; exact implementation boundary ({choiceImplementationModules.length} module(s), {exactImplementationDeclarations.length} declaration(s)) additionally allows Classical.choice"

end EffectsTest.Audit
