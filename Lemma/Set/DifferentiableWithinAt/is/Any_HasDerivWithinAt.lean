import Mathlib
import sympy.Basic
import sympy.analysis.Section_10_1
open Chapter10
open DifferentiableWithinAt


/--
[_root_.DifferentiableWithinAt.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_1.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {x₀ : ℝ}
  {f: ℝ → ℝ} :
-- imply
  DifferentiableWithinAt ℝ f X x₀ ↔ ∃ L, HasDerivWithinAt f L X x₀ :=
-- proof
  DifferentiableWithinAt.iff X x₀ f


-- created on 2026-10-22
