import sympy.tensor.Basic


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (A : Tensor α []) :
-- imply
  X / A = X / A.data[0] := by
-- proof
  simp [HDiv.hDiv]


-- created on 2025-09-26
