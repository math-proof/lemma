import stdlib.SEq
import sympy.Basic


@[main]
private lemma main
  {Vector : α → Sort v}
  {a b : Vector n}
-- given
  (h : a = b) :
-- imply
  a ≃ b := by
-- proof
  rw [h]


-- created on 2025-07-25
