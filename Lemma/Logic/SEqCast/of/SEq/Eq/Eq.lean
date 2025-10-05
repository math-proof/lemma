import stdlib.SEq
import sympy.Basic


@[main, comm 4]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h_a : n_a = n)
  (h_b : n_b = n)
  (h : a ≃ b)  :
-- imply
  cast (congr_arg Vector h_a) a ≃ b := by
-- proof
  simp_all [SEq]


-- created on 2025-10-05
