import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Icc (-1) 1)
  (hy : y ∈ Set.Icc (-1) 1)
  (h : Real.arccos x = Real.arccos y) :
-- imply
  x = y :=
-- proof
  Real.strictAntiOn_arccos.injOn hx hy h


-- created on 2022-01-23
