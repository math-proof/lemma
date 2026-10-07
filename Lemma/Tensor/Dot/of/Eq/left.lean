import sympy.matrices.expressions.matmul


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (t : Tensor α [n])
  (X Y : Tensor α [n, n])
  (h : X = Y) :
-- imply
  t @ X = t @ Y := by
-- proof
  exact congrArg (fun M : Tensor α [n, n] => t @ M) h


-- created on 2020-08-16
