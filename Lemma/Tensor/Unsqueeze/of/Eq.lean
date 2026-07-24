import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  {A B : Tensor α s}

-- given
  (h : A = B)
  (d : ℕ) :
-- imply
  A.unsqueeze d = B.unsqueeze d := by
-- proof
  subst h
  simp


-- created on 2026-01-10
