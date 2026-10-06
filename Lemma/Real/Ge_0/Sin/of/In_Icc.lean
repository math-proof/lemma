import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic

open Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Icc 0 π) :
-- imply
  Real.sin x ≥ 0 :=
-- proof
  Real.sin_nonneg_of_mem_Icc h


-- created on 2020-11-20
-- updated on 2023-05-14
