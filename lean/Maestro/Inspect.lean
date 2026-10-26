import Lean
open Lean Elab Command

/-- Trusted harness command; never supplied by a model. -/
elab "#maestro_inspect " n:ident : command => do
  let name ← resolveGlobalConstNoOverload n
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration {name}"
  let axioms ← collectAxioms name
  let ty ← liftTermElabM <| Meta.ppExpr info.type
  let data := Json.mkObj [
    ("name", toJson name.toString),
    ("type", toJson ty.pretty),
    ("axioms", toJson (axioms.map Name.toString)),
    ("is_theorem", toJson (match info with | .thmInfo _ => true | _ => false))]
  logInfo m!"MAESTRO_JSON:{data.compress}"
