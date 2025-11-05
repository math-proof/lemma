import Mathlib.Tactic
import sympy.parsing.parser
import sympy.printing.latex
open Lean Elab.Tactic Meta
set_option linter.unusedVariables false
-- print(_.values().__iter__().__next__())

def logInfo (hypId : Name) (hypType : TacticM Lean.Expr) (goal : Bool := false) := do
  let latex := (← Expr.toExpr (← hypType) [] 0).latex_tagged hypId (if goal then "red" else"green")
  Lean.logInfo m!"{Json.compress (Json.mkObj [(toString ((← getFileMap).toPosition ((← getRef).getPos?.getD 0)).line, latex)])}"


/--
A tactic `echo` that prints the types of specified hypotheses or the main goal.
usage:
- `echo h₁, h₂` prints the types of hypotheses `h₁` and `h₂`.
- `echo _` prints the type of the first wildcard hypothesis.
- `echo ⊢` prints the type of the main goal.
- `echo *` prints the types of all local hypotheses and the main goal.
-/
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

syntax "with_echo" tactic : tactic
elab_rules : tactic
  | `(tactic| with_echo $t) => do
    withMainContext do
      let history : Std.HashSet FVarId × Std.HashMap Name Lean.Expr ← (← getLCtx).decls.foldlM
        (fun ⟨set, map⟩ decl =>
          return if let some decl := decl then ⟨set.insert decl.fvarId, map.insert decl.userName decl.type⟩ else ⟨set, map⟩)
        ⟨{}, {}⟩
      let ⟨historySet, historyMap⟩ := history
      let goal ← getMainTarget
      evalTactic t
      withMainContext do
        let mut vars : Array Name := #[]
        let goal' ← getMainTarget
        -- isDefEq doesn't necessarily work for tactics : subst, unfold, rw, simp
        try
          if !(← isDefEq goal goal') then
            vars := vars.push `«⊢»
        catch e =>
            pure ()
        -- in case of duplicate hypothesis names, the current context map is needed, keeping only the most recent names
        let contextMap : Std.HashMap Name (FVarId × Lean.Expr) ← (← getLCtx).decls.foldlM
          (fun map decl =>
            return if let some decl := decl then map.insert decl.userName ⟨decl.fvarId, decl.type⟩ else map)
          {}
        for ⟨userName, fvarId, type'⟩ in contextMap do
          -- the newly created fvarId doesn't exist in history Set after the tactic application
          if !historySet.contains fvarId then
            if let some type := historyMap[userName]? then
              try
                if !(← isDefEq type type') then
                  vars := vars.push userName
              catch e =>
                  pure ()
        println! ("modified: " ++ " ".intercalate (vars.toList.map Name.toString))
