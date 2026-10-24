import Mathlib
import sympy.Basic
import sympy.analysis.Section_10_4
open Chapter9
open Chapter10
open HasDerivWithinAt


/--
[_root_.HasDerivWithinAt.of_inverse_of_zero_deriv](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_4.lean)
-/
@[path]
private lemma main
  {X Y: Set ℝ}
  {f g : ℝ → ℝ}
  {x₀ y₀: ℝ}
-- given
  (hfXY: ∀ x ∈ X, f x ∈ Y)
  (hgf: ∀ x ∈ X, g (f x) = x)
  (hx₀: x₀ ∈ X)
  (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f 0 X x₀) :
-- imply
  ¬ DifferentiableWithinAt ℝ g Y y₀ :=
-- proof
  HasDerivWithinAt.of_inverse_of_zero_deriv hfXY hgf hx₀ hfx₀ hcluster hf


-- created on 2026-10-22
