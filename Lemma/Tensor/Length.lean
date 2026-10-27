import Instance.Data.Holor.Tensor.Part2


@[path]
private lemma main
-- given
  (A B : Tensor α s) :
-- imply
  A.length = B.length := by
-- proof
  cases s <;>
  ·
    simp [Tensor.length]


-- created on 2025-10-08
