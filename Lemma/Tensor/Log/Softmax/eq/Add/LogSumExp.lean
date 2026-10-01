import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[main]
private lemma main
  [NeZero n]
  {x : Fin n → ℝ} :
-- imply
  (fun i => Real.log (Real.exp (x i) / ∑ j, Real.exp (x j))) = fun i => x i - Real.log (∑ j, Real.exp (x j)) := by
-- proof
  funext i
  have hs : ∑ j, Real.exp (x j) ≠ 0 := (Finset.sum_pos (fun j _ => Real.exp_pos (x j)) Finset.univ_nonempty).ne'
  rw [Real.log_div (Real.exp_pos (x i)).ne' hs, Real.log_exp]


-- created on 2026-09-27
