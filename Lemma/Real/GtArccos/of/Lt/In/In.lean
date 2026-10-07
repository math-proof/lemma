import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import sympy.Basic



@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x < y)
  (hx : x ∈ Set.Icc (-1) 1)
  (hy : y ∈ Set.Icc (-1) 1) :
-- imply
  Real.arccos x > Real.arccos y :=
-- proof
  Real.arccos_lt_arccos hx.1 h hy.2


-- created on 2020-11-30
