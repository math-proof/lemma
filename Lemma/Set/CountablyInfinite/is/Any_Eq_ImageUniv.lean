import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_1
open Chapter8
open Chapter8.CountablyInfinite


/--
[CountablyInfinite.iff_image_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X: Set A} :
-- imply
  CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' .univ :=
-- proof
  Chapter8.CountablyInfinite.iff_image_inj X


-- created on 2026-10-22
