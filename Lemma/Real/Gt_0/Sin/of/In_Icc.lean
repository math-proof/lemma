import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic

open Real


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Ioo 0 π) :
-- imply
  Real.sin x > 0 :=
-- proof
  Real.sin_pos_of_mem_Ioo h


-- created on 2020-11-19
