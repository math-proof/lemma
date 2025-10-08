import stdlib.SEq
import sympy.Basic


@[main, comm 2]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h : n_a = n_b')
  (h_eq : a ≃ b) :
-- imply
  cast (congrArg Vector h) a ≃ b := by
-- proof
  aesop


-- created on 2025-05-31
-- updated on 2025-06-28
