import torch.nn.functional.relu
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  max 0 x = relu x := by
-- proof
  unfold relu
  exact max_comm 0 x


-- created on 2021-12-19
