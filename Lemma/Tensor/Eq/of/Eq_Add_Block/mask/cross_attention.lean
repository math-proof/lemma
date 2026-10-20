import Mathlib.Analysis.SpecialFunctions.Exp
import sympy.Basic


@[path]
private lemma main
  {a : ℝ}
  {ξ : Bool} :
-- imply
  (if ξ then Real.exp a else 0) = (if ξ then (1 : ℝ) else 0) * Real.exp a := by
-- proof
  if h : ξ then
    simp [h]
  else
    simp [h]


-- created on 2020-12-29
-- updated on 2026-10-17
