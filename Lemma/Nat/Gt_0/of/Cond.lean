import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {p : Prop}
  [Decidable p]
-- given
  (h : p) :
-- imply
  (if p then (1 : ℝ) else 0) > 0 := by
-- proof
  rw [if_pos h]
  norm_num


-- created on 2023-11-05
