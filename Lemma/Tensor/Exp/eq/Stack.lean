import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[main]
private lemma main
  {n : ℕ}
  {h : Fin n → ℤ} :
-- imply
  Real.exp ∘ (fun i => (h i : ℝ)) = fun i => Real.exp (h i) :=
-- proof
  rfl


-- created on 2026-09-27
