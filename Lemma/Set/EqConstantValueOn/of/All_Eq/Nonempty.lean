import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_2
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.ConstantOn


/--
[ConstantOn.const_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {X: Set ℝ}
  {c:ℝ}
-- given
  (hX: X.Nonempty)
  (h: ∀ x ∈ X, f x = c) :
-- imply
  constant_value_on f X = c :=
-- proof
  Chapter11.ConstantOn.const_eq hX h


-- created on 2026-10-22
