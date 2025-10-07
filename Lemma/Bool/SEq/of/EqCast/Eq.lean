import stdlib.SEq
import sympy.Basic


@[main]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : n = m)
  (h_eq : cast (by congr) a = b) :
-- imply
  a ≃ b := by
-- proof
  aesop


-- created on 2025-07-25
-- updated on 2025-10-04
