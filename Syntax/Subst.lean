/-- One substitution `x = x₀` in the `Subst` sugar. -/
syntax substBinding := ident ppHardSpace "=" ppHardSpace term:36

/-- `Subst (expr | x = x₀ ∧ y = y₀)`: simultaneous substitution `x := x₀`, `y := y₀` in `expr`. -/
syntax:max (name := substSugar) "Subst" ppHardSpace "(" term ppHardSpace "|" ppSpace sepBy1(substBinding, " ∧ ") ")" : term

/-- `Subst f x₀ …`: plain application of the constant `«Subst»` (the name `Subst` is a keyword). -/
syntax:max (name := substApp) "Subst" (ppSpace colGt term:max)+ : term
