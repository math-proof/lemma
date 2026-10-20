import Mathlib.Analysis.SpecialFunctions.Exp
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {Q K V : Matrix (Fin n) (Fin n) ℝ}
  {H : ℝ} :
-- imply
  ∀ i, ∑ j, Real.exp (∑ t, Q i t * K j t + H * (if i = j then (1 : ℝ) else 0) + V i j - V i j) / ∑ k, Real.exp (∑ t, Q i t * K k t + H * (if i = k then (1 : ℝ) else 0) + V i k - V i k) = 1 := by
-- proof
  intro i
  have hden : ∑ k, Real.exp ((∑ t, Q i t * K k t + H * (if i = k then (1 : ℝ) else 0) + V i k - V i k)) ≠ 0 := by
    refine ne_of_gt (Finset.sum_pos (fun k _ => Real.exp_pos _) ?_)
    exact Finset.univ_nonempty
  rw [← Finset.sum_div]
  exact div_self hden


-- created on 2022-04-02
-- updated on 2026-10-17
