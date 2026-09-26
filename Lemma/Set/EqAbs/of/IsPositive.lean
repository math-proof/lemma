import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ioi 0) :
-- imply
  |x| = x :=
-- proof
  abs_of_pos h₀


-- created on 2026-09-26
