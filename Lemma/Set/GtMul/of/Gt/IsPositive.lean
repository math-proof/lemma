import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h : b < a)
  (hx : x ∈ Set.Ioi 0) :
-- imply
  b * x < a * x := by
-- proof
  exact mul_lt_mul_of_pos_right h hx


-- created on 2021-10-02
-- updated on 2023-05-15
