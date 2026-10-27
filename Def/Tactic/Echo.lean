import Mathlib.Tactic
import Def.Lean.Expr.Parser
import Def.Lean.PrettyPrinter.Latex.Part2
open Lean Elab.Tactic Meta
set_option linter.unusedVariables false


-- print(_.values().__iter__().__next__())

def logInfo (hypId : Name) (hypType : TacticM Lean.Expr) (goal : Bool := false) := do
  let latex := (← Expr.toExpr (← hypType) [] 0).latex_tagged hypId (if goal then "red" else"green")
  Lean.logInfo m!"{Json.compress (Json.mkObj [(toString ((← getFileMap).toPosition ((← getRef).getPos?.getD 0)).line, latex)])}"

