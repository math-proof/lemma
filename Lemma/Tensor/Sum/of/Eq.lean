import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {A B : Tensor α s}
-- given
  (h : A = B)
  (i : ℕ) :
-- imply
  A.sum i = B.sum i := by
-- proof
  subst h
  simp


-- created on 2026-01-10
