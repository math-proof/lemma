import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Iio 0) :
-- imply
  |x| = -x :=
-- proof
  abs_of_neg h₀


-- created on 2026-09-26
