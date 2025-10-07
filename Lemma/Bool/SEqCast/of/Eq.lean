import stdlib.SEq
import sympy.Basic


@[main, comm]
private lemma main
  {Vector : α → Sort v}
-- given
  (h : n = n')
  (a : Vector n) :
-- imply
  cast (by rw [h]) a ≃ a := by
-- proof
  simp_all [SEq]


-- created on 2025-07-25
