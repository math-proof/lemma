import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ}
-- given
  (hx : x ∈ Set.Iio 0)
  (hlt : g x < h x) :
-- imply
  h x * x < g x * x := by
-- proof
  exact mul_lt_mul_of_neg_right hlt hx


-- created on 2023-10-15
