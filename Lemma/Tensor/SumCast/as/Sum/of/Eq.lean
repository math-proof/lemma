import stdlib.SEq
import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (h : s = s')
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).sum i ≃ X.sum i := by
-- proof
  subst h
  rfl


-- created on 2025-10-31
