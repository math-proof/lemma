import torch.nn.functional.relu
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  relu x ≥ x := by
-- proof
  unfold relu
  exact le_max_left _ _


-- created on 2021-12-18
