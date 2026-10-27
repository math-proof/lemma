import Mathlib.Analysis.Calculus.Gradient.Basic


/-- Strip outer term parentheses so `∇[θ] (F θ)` and `∇[θ] F θ` share one match. -/
partial def GradSugar.stripParen : Lean.TSyntax `term → Lean.MacroM (Lean.TSyntax `term)
  | `(($e)) => stripParen e
  | e => pure e

