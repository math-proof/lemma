import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[main]
private lemma main
  [NeZero n]
  {x : Fin m → Fin n → ℝ} :
-- imply
  (fun i j => Real.exp (x i j)) = fun i j => Real.exp (x i j) / (∑ k, Real.exp (x i k)) * ∑ k, Real.exp (x i k) := by
-- proof
  funext i j
  rw [div_mul_cancel₀]
  exact (Finset.sum_pos (fun k _ => Real.exp_pos (x i k)) Finset.univ_nonempty).ne'


-- created on 2022-01-10
