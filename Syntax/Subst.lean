import Abbrev.Subst

/-- One substitution `x = x₀` in the `Subst` sugar. -/
syntax substBinding := ident ppHardSpace "=" ppHardSpace term:36

/-- `Subst (expr | x = x₀ ∧ y = y₀)`: simultaneous substitution `x := x₀`, `y := y₀` in `expr`. -/
syntax:max (name := substSugar) "Subst" ppHardSpace "(" term ppHardSpace "|" ppSpace sepBy1(substBinding, " ∧ ") ")" : term

/-- `Subst f x₀ …`: plain application of the constant `«Subst»` (the name `Subst` is a keyword). -/
syntax:max (name := substApp) "Subst" (ppSpace colGt term:max)+ : term

macro_rules
  | `(Subst ($body | $bs∧*)) => do
    let bs := bs.getElems
    let xs ← bs.mapM fun
      | `(substBinding| $x:ident = $_) => pure x
      | _ => Lean.Macro.throwUnsupported
    let vs ← bs.mapM fun
      | `(substBinding| $_:ident = $v) => pure v
      | _ => Lean.Macro.throwUnsupported
    -- with `n` values, `Subst f x₀ : β` is applied to `n - 1` more: fix `β := _ → ⋯ → _` up front so the
    -- application elaborates before `f` does
    let mut β ← `(_)
    -- avoid `vs[1:]` (parsed as open-slice once stdlib.List is imported)
    for _ in vs.extract 1 vs.size do
      β ← `(_ → $β)
    `(«Subst» (β := $β) (fun $xs* ↦ $body) $vs*)

macro_rules
  | `(Subst $args*) => `(«Subst» $args*)
