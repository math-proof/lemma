import sympy.tensor.functions


@[main]
private lemma main
  [Cos α]
-- given
  (X : Tensor α s) :
-- imply
  X.cos.data = X.data.cos :=
-- proof
  rfl


-- created on 2026-09-02
