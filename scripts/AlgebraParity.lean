import Lean
import Effects.Algebra.Signature
import Effects.Algebra.MonadLaws
import Effects.Algebra.Program
import Effects.Algebra.Handler
import Effects.Algebra.Laws
import Effects.Algebra.Sum
import Effects.Algebra.Universal
import Effects.Algebra.Handler.Composition
import Effects.Algebra.Handler.Category

/-!
# Signature-and-axiom parity receipt

Prints one row per constant compiled from the nine algebra modules: name,
module, kind, universe parameters, type, definition value (definitions only),
and axiom set, all with `pp.all` and with the library root replaced by
`«ROOT»`. Run against `Effects` here and against `Effect4` at the source
commit (with `Effects` rewritten to `Effect4` in this file); the two outputs
must be byte-identical. Equal counts are not accepted as a substitute.

Usage: `PARITY_OUT=<file> lake env lean scripts/AlgebraParity.lean`
-/

open Lean Meta Elab

namespace AlgebraParity

def root : String := "Effects"

def modules : List Name :=
  [ `Effects.Algebra.Signature
  , `Effects.Algebra.MonadLaws
  , `Effects.Algebra.Program
  , `Effects.Algebra.Handler
  , `Effects.Algebra.Laws
  , `Effects.Algebra.Sum
  , `Effects.Algebra.Universal
  , `Effects.Algebra.Handler.Composition
  , `Effects.Algebra.Handler.Category ]

/-- The root occurs as a name prefix (`Effects.`), and, in the three auxiliary
declarations Lean generates for the `⊕ₛ` notation (syntax kind, macro rules,
unexpander), as a string literal (`"Effects"`) and inside underscore-joined
auxiliary names (`_Effects_`). All three spellings are the rename's own
footprint and are replaced; nothing else is. -/
def normalise (s : String) : String :=
  (((s.replace (root ++ ".") "«ROOT».")
    |>.replace ("\"" ++ root ++ "\"") "\"«ROOT»\"")
    |>.replace ("_" ++ root ++ "_") "_«ROOT»_")
    |>.replace "\n" " "

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"

def ppAll (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.all true) (ppExpr e)
  return normalise (toString fmt)

run_elab do
  let env ← getEnv
  let some out ← liftM (IO.getEnv "PARITY_OUT")
    | throwError "PARITY_OUT is unset"
  let mut rows : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    unless modules.contains modName do continue
    let ty ← ppAll info.type
    let value ← match info with
      | .defnInfo d => ppAll d.value
      | _ => pure ""
    let axioms ← collectAxioms name
    let axiomNames := (axioms.map toString).qsort (· < ·)
    let levels := String.intercalate "," (info.levelParams.map toString)
    rows := rows.push <| String.intercalate "\t"
      [ normalise name.toString, normalise modName.toString, kindOf info, levels
      , ty, value, String.intercalate "," axiomNames.toList ]
  let sorted := rows.qsort (· < ·)
  liftM <| IO.FS.writeFile out (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"algebra parity: {sorted.size} constants written to {out}"

end AlgebraParity
