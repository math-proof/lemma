import stdlib.SEq
import sympy.Basic


@[main, comm 2]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h_n : n_a = n_b)
  (h : a ≃ b) :
-- imply
  cast (congr_arg Vector h_n) a = b := by
-- proof
  simp [SEq] at h ⊢
  aesop


-- created on 2025-10-05
