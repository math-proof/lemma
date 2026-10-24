import Mathlib
import sympy.Basic
import sympy.analysis.Section_10_1
open Chapter10


/--
[derivative_unique'](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_1.lean)
-/
@[path]
private lemma main
  {x₀ : ℝ}
  {X: Set ℝ}
  {x₀ : ℝ}
  {f: ℝ → ℝ}
  {L :ℝ}
-- given
  (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  (hL: HasDerivWithinAt f L X x₀)
  (hdiff : DifferentiableWithinAt ℝ f X x₀) :
-- imply
  L = derivWithin f X x₀ :=
-- proof
  Chapter10.derivative_unique' X hx₀ hL hdiff


-- created on 2026-10-22
