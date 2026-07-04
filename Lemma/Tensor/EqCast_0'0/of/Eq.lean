import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Zero α]
  {s s' : List ℕ}
-- given
  (h : s = s') :
-- imply
  cast (congrArg (Tensor α) h) 0 = 0 := by
-- proof
  aesop


-- created on 2025-11-30
