import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Icc (-Real.pi) 0) :
-- imply
  Real.sin x ≤ 0 :=
-- proof
  Real.sin_nonpos_of_nonpos_of_neg_pi_le h.2 h.1


-- created on 2020-11-20
