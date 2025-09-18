import sympy.tensor.Basic
import Lemma.Basic


@[main]
private lemma main
  {t : Tensor α s}
-- given
  (h : t.length > 0) :
-- imply
  s.length > 0 := by
-- proof
  by_contra h'
  simp at h'
  simp [Tensor.length] at h
  cases s
  contradiction
  simp_all


-- created on 2025-06-14
