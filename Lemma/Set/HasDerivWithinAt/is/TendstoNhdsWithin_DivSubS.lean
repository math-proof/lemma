import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_10_1.Part2
open Chapter10
open HasDerivWithinAt


/--
[_root_.HasDerivWithinAt.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_1.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {x₀ : ℝ}
  {f: ℝ → ℝ}
  {L:ℝ} :
-- imply
  HasDerivWithinAt f L X x₀ ↔ (nhdsWithin x₀ (X \ {x₀})).Tendsto (fun x ↦ (f x - f x₀) / (x - x₀))
    (nhds L) :=
-- proof
  HasDerivWithinAt.iff X x₀ f L


-- created on 2026-10-22
