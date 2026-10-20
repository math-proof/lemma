import Mathlib.Analysis.SpecialFunctions.Exp
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {A : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  ∀ i, ∑ j, Real.exp (A i j) / ∑ k, Real.exp (A i k) = 1 := by
-- proof
  intro i
  have hden : ∑ k, Real.exp ((A i k)) ≠ 0 := by
    refine ne_of_gt (Finset.sum_pos (fun k _ => Real.exp_pos _) ?_)
    exact Finset.univ_nonempty
  rw [← Finset.sum_div]
  exact div_self hden


-- created on 2023-09-15
-- updated on 2026-10-17
