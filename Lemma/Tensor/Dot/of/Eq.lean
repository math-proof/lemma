import sympy.tensor.tensor


@[main]
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


@[main]
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


-- created on 2021-10-04
-- updated on 2026-08-23
