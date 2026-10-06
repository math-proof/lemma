import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ}
-- given
  (hx : x ∈ Set.Ioi 0)
  (hlt : h x < g x) :
-- imply
  h x * x < g x * x := by
-- proof
  exact mul_lt_mul_of_pos_right hlt hx


-- created on 2023-10-15
