import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_3
open Chapter9
open Chapter9.Convergesto


/--
[Convergesto.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_3.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f: ℝ → ℝ}
  {L x₀ : ℝ} :
-- imply
  Convergesto X f L x₀ ↔ (nhdsWithin x₀ X).Tendsto f (nhds L) :=
-- proof
  Chapter9.Convergesto.iff X f L x₀


-- created on 2026-10-22
