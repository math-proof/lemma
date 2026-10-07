import Mathlib
import sympy.Basic
open Set Real



@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ioo 0 π) :
-- imply
  x ^ 2 * (x + sin x) / (x - sin x) > π ^ 2 := by
-- proof
  sorry


-- created on 2026-10-07
