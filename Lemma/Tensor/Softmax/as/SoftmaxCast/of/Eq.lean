import sympy.tensor.functions
import stdlib.SEq
import sympy.tensor.Basic


@[main, comm]
private lemma main
  [Exp α]
  {s : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  X.softmax i ≃ (cast (congrArg (Tensor α) h) X).softmax i := by
-- proof
  subst h
  rfl


-- created on 2025-10-31
