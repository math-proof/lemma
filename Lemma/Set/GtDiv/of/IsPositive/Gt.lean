import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ}
-- given
  (hx : x ∈ Set.Ioi 0)
  (hlt : h x < g x) :
-- imply
  h x / x < g x / x := by
-- proof
  exact div_lt_div_of_pos_right hlt hx


-- created on 2023-10-15
