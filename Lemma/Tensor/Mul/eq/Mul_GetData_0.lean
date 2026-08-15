import sympy.tensor.Basic


@[main]
private lemma main
  [Mul α]
-- given
  (X : Tensor α s)
  (A : Tensor α []) :
-- imply
  X * A = X * A.data[0] := by
-- proof
  simp [HMul.hMul]


-- created on 2026-08-15
