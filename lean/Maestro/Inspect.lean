import Lean
open Lean Elab Command

/-- Trusted harness command; never supplied by a model.
`axioms` are transitive; `direct_sorry` reports whether this declaration's own
proof term mentions `sorryAx`, which separates an assembled parent waiting on
children from a declaration whose own proof is unfinished. -/
elab "#maestro_inspect " n:ident : command => do
  let name ← resolveGlobalConstNoOverload n
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration {name}"
  let axioms ← collectAxioms name
  -- Readable type for models only; the falsifier uses `type_of%`, never this text.
  let ty ← liftTermElabM <| Meta.ppExpr info.type
  let direct := match info.value? (allowOpaque := true) with
    | some v => v.getUsedConstants.contains ``sorryAx
    | none => true
  let data := Json.mkObj [
    ("name", toJson name.toString),
    ("type", toJson ty.pretty),
    ("type_hash", toJson (toString info.type.hash)),
    ("axioms", toJson (axioms.map Name.toString)),
    ("direct_sorry", toJson direct),
    ("is_theorem", toJson (match info with | .thmInfo _ => true | _ => false))]
  logInfo m!"MAESTRO_JSON:{data.compress}"
