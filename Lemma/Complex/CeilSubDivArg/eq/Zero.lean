import Lemma.Complex.CeilSubDivArg.eq.Zero.of.Gt_0
open Complex


@[main]
private lemma main
  {z : ℂ}
  {n : ℕ} :
-- imply
  ⌈arg z / (2 * n * π) - 1 / 2⌉ = 0 := by
-- proof
  if h_pos : n > 0 then
    exact CeilSubDivArg.eq.Zero.of.Gt_0 (z := z) h_pos
  else
    simp at h_pos
    rw [h_pos]
    norm_num


-- created on 2025-03-01
-- updated on 2025-03-02
