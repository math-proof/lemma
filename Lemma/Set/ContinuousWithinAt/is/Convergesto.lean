import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_4.Part2
open Chapter9
open Chapter9.ContinuousWithinAt


/--
[ContinuousWithinAt.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_4.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f: ℝ → ℝ}
  {x₀:ℝ} :
-- imply
  ContinuousWithinAt f X x₀ ↔ Convergesto X f (f x₀) x₀ :=
-- proof
  Chapter9.ContinuousWithinAt.iff X f x₀


-- created on 2026-10-22
