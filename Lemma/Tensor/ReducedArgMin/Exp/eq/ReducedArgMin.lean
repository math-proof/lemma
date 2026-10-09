import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Analysis.SpecialFunctions.Exp


@[path]
private lemma main
  [NeZero n]
  {x : Fin n → ℝ} :
-- imply
  ArgMin Set.univ (fun j => Real.exp (x j)) = ArgMin Set.univ x := by
-- proof
  unfold ArgMin
  congr 1
  funext k
  simp only [Real.exp_le_exp]


-- created on 2026-10-08
