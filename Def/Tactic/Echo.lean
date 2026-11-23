module

public import Mathlib.Tactic
public import Def.Lean.Expr.Parser
public import Def.Lean.PrettyPrinter.Json

@[expose] public section

open Lean Elab.Tactic Meta
set_option linter.unusedVariables false


-- print(_.values().__iter__().__next__())

def logInfo (hypId : Name) (hypType : TacticM Lean.Expr) (goal : Bool := false) := do
  let expr ← Expr.toExpr (← hypType) [] 0
  let latex := expr.latex_tagged hypId (if goal then "red" else "green")
  let line := ((← getFileMap).toPosition ((← getRef).getPos?.getD 0)).line
  let fields := [(toString line, toJson latex)]
  let fields ←
    if goal && (← IO.getEnv "LEAN_ECHO_SEARCH_JSON") == some "1" then
      pure (fields ++ [("struct", expr.toJson)])
    else
      pure fields
  Lean.logInfo m!"{Json.compress (Json.mkObj fields)}"

