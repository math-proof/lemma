import torch.nn.functional.relu
import sympy.Basic


@[path]
private lemma main
  {i l : ℤ}
-- given
  (h : i ≥ l) :
-- imply
  relu (i + 1 - l) = i + 1 - l := by
-- proof
  unfold relu
  exact max_eq_left (by omega)


-- created on 2022-04-01
