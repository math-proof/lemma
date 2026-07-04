import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
-- given
  (h_s : s = s')
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).length = X.length := by
-- proof
  aesop


-- created on 2026-07-03
