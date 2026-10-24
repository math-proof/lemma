import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_2
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.ConstantOn


/--
[ConstantOn.congr'](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f g: ℝ → ℝ}
  {X: Set ℝ}
-- given
  (hf: ConstantOn f X)
  (h: ∀ x ∈ X, f x = g x) :
-- imply
  ConstantOn g X :=
-- proof
  Chapter11.ConstantOn.congr' hf h


-- created on 2026-10-22
