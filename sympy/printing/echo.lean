import Mathlib.Tactic
import sympy.parsing.parser
import sympy.printing.latex
open Lean Elab.Tactic Meta
set_option linter.unusedVariables false
-- print(_.values().__iter__().__next__())

def logInfo (hypId : Name) (hypType : TacticM Lean.Expr) (goal : Bool := false) := do
  let latex := (← Expr.toExpr (← hypType) [] 0).latex_tagged hypId (if goal then "red" else"green")
  Lean.logInfo m!"{Json.compress (Json.mkObj [(toString ((← getFileMap).toPosition ((← getRef).getPos?.getD 0)).line, latex)])}"


syntax (name := echo) "echo" ((ident <|> "_" <|> "⊢"),+ <|> "*") : tactic

@[tactic echo]
def evalEcho : Tactic := fun stx => do
  -- Extract the identifiers from the syntax
  withMainContext do
    let sepArgs := stx[1].getSepArgs
    for identStx in sepArgs do
      -- let hypId := identStx.getId
      let hypId :=
        match identStx with
        | .node _ (.str `token _) #[.atom _ val]
        | .atom _ val
        | .ident _ _ (.str _ val) _ => val
        | _ => ""
      -- println! s!"identStx = {identStx}, hypId = {hypId}"
      if hypId == "*" then
        -- Print all local hypotheses
        for decl in (← getLCtx).decls do
          if let some decl := decl then
            if decl.userName != `main then
              let hypType := inferType decl.toExpr
              if ← (← hypType).is_Prop then
                logInfo decl.userName hypType
        -- Print the main target
        logInfo default getMainTarget true
      else if hypId == "⊢" then
        if sepArgs.size > 1 then
          -- Print the main target
          logInfo default getMainTarget true
        else
          -- Print the all goals
          let gs ← getGoals
          for g in gs do
            let decl ← g.getDecl
            logInfo decl.userName (instantiateMVars decl.type) true
      else if hypId == "_" then
        -- Print the first wild card hypothesis
        for decl in (← getLCtx).decls do
          if let some decl := decl then
            if let some (.succ index) := decl.userName.components.idxOf? `«_@» then
              let hypType := inferType decl.toExpr
              if ← (← hypType).is_Prop then
                logInfo decl.userName hypType
                break
      else if hypId != "" then
        -- Print the specific local hypothesis
        let hypId := Name.mkSimple hypId
        try
          logInfo hypId (inferType (← getLocalDeclFromUserName hypId).toExpr)
        catch e =>
          Lean.logInfo m!"{e.toMessageData}"
