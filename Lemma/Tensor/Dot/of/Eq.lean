import Instance.LinearAlgebra.Matrix.Matmul


@[path]
private lemma left
  [Mul α] [Add α] [Zero α]
  {X Y : Tensor α s}
  {lhs : Tensor α s'}
-- given
  (h : X = Y) :
-- imply
  lhs @ X = lhs @ Y := by
-- proof
  rw [h]


@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
  {X Y : Tensor α s}
  {rhs : Tensor α s'}
-- given
  (h : X = Y) :
-- imply
  X @ rhs = Y @ rhs := by
-- proof
  rw [h]


-- created on 2020-08-16
-- updated on 2026-10-26
