import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_9_8
open Chapter9
open Chapter9.AntitoneOn


/--
[AntitoneOn.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_8.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f: ℝ → ℝ} :
-- imply
  AntitoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≤ f x :=
-- proof
  Chapter9.AntitoneOn.iff f


-- created on 2026-10-22
