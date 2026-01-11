import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  {A B : Tensor α s}
-- given
  (h : A = B)
  (n : ℕ)
  (d : Fin s.length) :
-- imply
  A.repeat n d = B.repeat n d := by
-- proof
  subst h
  simp


-- created on 2026-01-10
