import stdlib.SEq
import sympy.Basic


@[main, comm 2]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : n = m')
  (h_eq : a ≃ b) :
-- imply
  cast (congr_arg Vector h) a ≃ b := by
-- proof
  aesop


-- created on 2025-05-31
-- updated on 2025-06-28
