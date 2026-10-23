import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_1
open Chapter9


/--
[isClosed_iff_limits_mem](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_1.lean)
-/
@[path]
private lemma main
  {X: Set ℝ} :
-- imply
  IsClosed X ↔ ∀ (a:ℕ → ℝ) (L:ℝ), (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds L) → L ∈ X :=
-- proof
  Chapter9.isClosed_iff_limits_mem X


-- created on 2026-10-22
