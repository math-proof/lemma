import sympy.Basic
import sympy.tensor.Basic
import sympy.tensor.functions


@[main, comm]
private lemma main
  [Exp α]
  {s : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).softmax i = cast (congrArg (Tensor α) h) (X.softmax i) := by
-- proof
  subst h
  rfl


-- created on 2025-11-17
