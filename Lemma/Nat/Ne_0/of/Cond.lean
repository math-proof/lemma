import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {p : Prop}
  [Decidable p]
-- given
  (h : p) :
-- imply
  (if p then 1 else 0 : ℤ) ≠ 0 := by
-- proof
  rw [if_pos h]
  exact one_ne_zero


-- created on 2023-11-05
