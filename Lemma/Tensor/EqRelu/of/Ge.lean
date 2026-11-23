import Def.Data.Tensor.Relu


@[path]
private lemma main
  {i l : ℤ}
-- given
  (h : i ≥ l) :
-- imply
  relu (i + 1 - l) = i + 1 - l := by
-- proof
  unfold relu
  apply max_eq_left
  linarith [h]


-- created on 2022-04-01
