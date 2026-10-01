import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b l : ℝ}
-- given
  (hl : l < 0)
  (hab : a ≤ b) :
-- imply
  min (max (l * x) (l * b)) (l * a) = l * min (max x a) b := by
-- proof
  have e1 : max (l * x) (l * b) = l * min x b := by
    rcases le_total x b with h | h
    · rw [min_eq_left h, max_eq_left (mul_le_mul_of_nonpos_left h hl.le)]
    · rw [min_eq_right h, max_eq_right (mul_le_mul_of_nonpos_left h hl.le)]
  have e2 : ∀ m, min (l * m) (l * a) = l * max m a := by
    intro m
    rcases le_total m a with h | h
    · rw [max_eq_right h, min_eq_right (mul_le_mul_of_nonpos_left h hl.le)]
    · rw [max_eq_left h, min_eq_left (mul_le_mul_of_nonpos_left h hl.le)]
  rw [e1, e2, max_comm (min x b) a, max_min_distrib_left, max_eq_right hab, max_comm]


-- created on 2026-09-27
