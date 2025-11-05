import Mathlib.Tactic
import sympy.parsing.parser
import sympy.printing.latex
open Lean Elab.Tactic Meta
set_option linter.unusedVariables false
-- print(_.values().__iter__().__next__())

def logInfo (hypId : Name) (hypType : TacticM Lean.Expr) (goal : Bool := false) := do
  let latex := (← Expr.toExpr (← hypType) [] 0).latex_tagged hypId (if goal then "red" else"green")
  Lean.logInfo m!"{Json.compress (Json.mkObj [(toString ((← getFileMap).toPosition ((← getRef).getPos?.getD 0)).line, latex)])}"

declare_syntax_cat echo_ident
syntax ident : echo_ident
syntax "_" : echo_ident
syntax "⊢" : echo_ident

declare_syntax_cat echo_expr
syntax echo_ident,+ : echo_expr
syntax "*" tactic : echo_expr

/--
A tactic `echo` that prints the types of specified hypotheses or the main goal.
usage:
- `echo h₁, h₂, ⊢` prints the types of hypotheses `h₁`, `h₂` and the main goal.
- `echo _` prints the type of the first wildcard hypothesis.
- `echo * simp at *` prints the types of all local hypotheses affected by the tactic `simp at *`.
-/
syntax (name := echo) "echo" echo_expr : tactic

elab_rules : tactic
  | `(tactic| echo $[$hyps:echo_ident],*) => do
  withMainContext do
    for hyp in hyps do
      match hyp with
      | `(echo_ident| ⊢) => do
        if hyps.size > 1 then
          -- Print the main target
          logInfo default getMainTarget true
        else
          -- Print the all goals
          let gs ← getGoals
          for g in gs do
            let decl ← g.getDecl
            logInfo decl.userName (instantiateMVars decl.type) true
      | `(echo_ident| _) => do
        -- Print the first wild card hypothesis
        for decl in (← getLCtx).decls do
          if let some decl := decl then
            if let some (.succ index) := decl.userName.components.idxOf? `«_@» then
              let hypType := inferType decl.toExpr
              if ← (← hypType).is_Prop then
                logInfo decl.userName hypType
                break
      | `(echo_ident| $h:ident) => do
        -- Print the specific local hypothesis
        try
          logInfo h.getId (inferType (← getLocalDeclFromUserName h.getId).toExpr)
        catch e =>
          logInfo m!"{e.toMessageData}"
      | _ =>
        throwError "unreachable"

  | `(tactic| echo * $t) => do
  withMainContext do
    let history : Std.HashSet FVarId × Std.HashMap Name Lean.Expr ← (← getLCtx).decls.foldlM
      (fun ⟨set, map⟩ decl =>
        return if let some decl := decl then ⟨set.insert decl.fvarId, map.insert decl.userName decl.type⟩ else ⟨set, map⟩)
      ⟨{}, {}⟩
    let ⟨historySet, historyMap⟩ := history
    let goal ← getMainTarget
    evalTactic t
    withMainContext do
      let goal' ← getMainTarget
      -- isDefEq doesn't necessarily work for tactics : subst, unfold, rw, simp
      try
        if !(← isDefEq goal goal') then
          logInfo default getMainTarget true
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
                try
                  logInfo userName (inferType (← getLocalDeclFromUserName userName).toExpr)
                catch e =>
                  logInfo m!"{e.toMessageData}"
              else
                pure ()
            catch e =>
              pure ()
