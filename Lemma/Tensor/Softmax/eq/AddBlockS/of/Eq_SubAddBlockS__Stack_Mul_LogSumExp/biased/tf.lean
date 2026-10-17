import Mathlib.Analysis.SpecialFunctions.Exp
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {A : Matrix (Fin n) (Fin n) ℝ}
  {H : ℝ} :
-- imply
  ∀ i, ∑ j, Real.exp (A i j + H * (if i = j then (1 : ℝ) else 0)) / ∑ k, Real.exp (A i k + H * (if i = k then (1 : ℝ) else 0)) = 1 := by
-- proof
  intro i
  have hden : ∑ k, Real.exp ((A i k + H * (if i = k then (1 : ℝ) else 0))) ≠ 0 := by
    refine ne_of_gt (Finset.sum_pos (fun k _ => Real.exp_pos _) ?_)
    exact Finset.univ_nonempty
  rw [← Finset.sum_div]
  exact div_self hden


-- created on 2026-10-11
-- updated on 2026-10-17
