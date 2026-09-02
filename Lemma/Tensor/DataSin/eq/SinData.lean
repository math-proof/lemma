import sympy.tensor.functions


@[main]
private lemma main
  [Sin α]
-- given
  (X : Tensor α s) :
-- imply
  X.sin.data = X.data.sin :=
-- proof
  rfl


-- created on 2026-09-02
