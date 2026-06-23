import stdlib.SEq
import sympy.tensor.Basic


@[main, comm 1, cast]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) h) X).data ≃ X.data := by
-- proof
  aesop


-- created on 2025-07-24
