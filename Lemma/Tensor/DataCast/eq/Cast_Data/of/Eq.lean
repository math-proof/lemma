import sympy.tensor.Basic
import sympy.Basic


@[main, comm 1]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) h) X).data = cast (congrArg (List.Vector α) (congrArg List.prod h)) X.data := by
-- proof
  aesop


-- created on 2025-07-24
