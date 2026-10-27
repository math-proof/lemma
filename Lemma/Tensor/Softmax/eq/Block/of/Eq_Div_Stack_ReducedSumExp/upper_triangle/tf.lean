import Mathlib.Analysis.SpecialFunctions.Exp
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {l u : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  ∀ i, ∑ j, Real.exp (if j.1 ≤ i.1 + u ∧ i.1 ≤ j.1 + l then A i j else 0) / ∑ k, Real.exp (if k.1 ≤ i.1 + u ∧ i.1 ≤ k.1 + l then A i k else 0) = 1 := by
-- proof
  intro i
  have hden : ∑ k, Real.exp ((if k.1 ≤ i.1 + u ∧ i.1 ≤ k.1 + l then A i k else 0)) ≠ 0 := by
    refine ne_of_gt (Finset.sum_pos (fun k _ => Real.exp_pos _) ?_)
    exact Finset.univ_nonempty
  rw [← Finset.sum_div]
  exact div_self hden


-- created on 2022-01-01
-- updated on 2026-10-26
