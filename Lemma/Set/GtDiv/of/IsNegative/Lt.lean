import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ}
-- given
  (hx : x ∈ Set.Iio 0)
  (hlt : g x < h x) :
-- imply
  h x / x < g x / x := by
-- proof
  exact div_lt_div_of_neg_of_lt hx hlt


-- created on 2023-10-15
