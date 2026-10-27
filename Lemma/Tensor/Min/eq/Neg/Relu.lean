import Def.Data.Holor.Relu


@[path]
private lemma main
  {x : ℝ} :
-- imply
  min (0 : ℝ) x = -relu (-x) := by
-- proof
  unfold relu
  rw [min_comm, ← min_neg_neg]
  simp


-- created on 2021-12-25
-- updated on 2026-10-26
