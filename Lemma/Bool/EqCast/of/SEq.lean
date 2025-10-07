import stdlib.SEq
import sympy.Basic


@[main, comm 1]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h_eq : a ≃ b) :
-- imply
  cast (by rw [h_eq.left]) a = b := by
-- proof
  simp [SEq] at h_eq
  aesop


-- created on 2025-07-25
