import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_1.Part3
open Chapter9
open Chapter9.LimitPt


/--
[LimitPt.iff_limit](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_1.lean)
-/
@[path]
private lemma main
  {x:ℝ}
  {X: Set ℝ} :
-- imply
  LimitPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X \ {x}) ∧ Filter.atTop.Tendsto a (nhds x) :=
-- proof
  Chapter9.LimitPt.iff_limit x X


-- created on 2026-10-22
