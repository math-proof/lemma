import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[main]
private lemma main
  {n : ℕ}
  {a : Fin n → ℝ} :
-- imply
  (fun j => Real.exp (a j)) = Real.exp ∘ a :=
-- proof
  rfl


-- created on 2026-09-27
