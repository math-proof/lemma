import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_8
open Chapter9
open Chapter9.MonotoneOn


/--
[MonotoneOn.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_8.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f: ℝ → ℝ} :
-- imply
  MonotoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≥ f x :=
-- proof
  Chapter9.MonotoneOn.iff f


-- created on 2026-10-22
