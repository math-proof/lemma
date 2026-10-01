import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Analysis.SpecialFunctions.Exp


@[main]
private lemma main
  [NeZero n]
  {x : Fin n → ℝ} :
-- imply
  ArgMax Set.univ (fun j => Real.exp (x j)) = ArgMax Set.univ x := by
-- proof
  unfold ArgMax
  congr 1
  funext k
  simp only [Real.exp_le_exp]


-- created on 2021-12-20
