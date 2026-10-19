import torch.nn.functional.relu


@[path]
private lemma main
  {x : ℝ} :
-- imply
  min (0 : ℝ) x = -relu (-x) := by
-- proof
  unfold relu
  rw [min_comm, ← min_neg_neg]
  simp


-- created on 2026-10-11
-- updated on 2026-10-17
