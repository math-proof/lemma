import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_10_1.Part2
open Chapter10


/--
[derivative_unique](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_1.lean)
-/
@[path]
private lemma main
  {x₀ : ℝ}
  {X: Set ℝ}
  {x₀ : ℝ}
  {f: ℝ → ℝ}
  {L L':ℝ}
-- given
  (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  (hL: HasDerivWithinAt f L X x₀)
  (hL': HasDerivWithinAt f L' X x₀) :
-- imply
  L = L' :=
-- proof
  Chapter10.derivative_unique hx₀ hL hL'


-- created on 2026-10-22
