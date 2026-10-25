import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_9_9
open Chapter6 Filter
open Chapter9
open Chapter9.UniformContinuousOn


/--
[UniformContinuousOn.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_9.lean)
-/
@[path]
private lemma main
  {f: ℝ → ℝ}
  {X:Set ℝ} :
-- imply
  UniformContinuousOn f X  ↔
    ∀ ε > (0:ℝ), ∃ δ > (0:ℝ), ∀ x₀ ∈ X, ∀ x ∈ X, δ.Close x x₀ → ε.Close (f x) (f x₀) :=
-- proof
  Chapter9.UniformContinuousOn.iff f X


-- created on 2026-10-22
