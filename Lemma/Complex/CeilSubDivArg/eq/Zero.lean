import Lemma.Complex.CeilSubDivArg.eq.Zero.of.Gt_0
open Complex


@[main]
private lemma main
  {z : ℂ}
  {n : ℕ} :
-- imply
  ⌈arg z / (2 * n * π) - 1 / 2⌉ = 0 := by
-- proof
  by_cases h_Gt_0 : n > 0
  exact CeilSubDivArg.eq.Zero.of.Gt_0 (z := z) h_Gt_0
  simp at h_Gt_0
  rw [h_Gt_0]
  norm_num


-- created on 2025-03-01
-- updated on 2025-03-02
