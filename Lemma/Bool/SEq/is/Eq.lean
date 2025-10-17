import stdlib.SEq
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  {Vector : α → Sort v}
-- given
  (a b : Vector n) :
-- imply
  a ≃ b ↔ a = b := by
-- proof
  constructor <;>
    intro h
  .
    simp [SEq] at h
    assumption
  .
    rw [h]


-- created on 2025-07-25
