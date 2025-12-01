import sympy.tensor.tensor


@[main]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α s)
  (i : Fin s.length)
  (d : ℤ) :
-- imply
  (A * B).permute i d = A.permute i d * B.permute i d := by
-- proof
  sorry


-- created on 2025-12-01
