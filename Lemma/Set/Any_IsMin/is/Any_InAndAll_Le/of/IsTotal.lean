import Mathlib
import sympy.Basic
import Def.Analysis.Section_8_5.Part4
open Chapter8
open Chapter8.IsMin


/--
[IsMin.iff_lowerbound'](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  {X:Type} [PartialOrder X]
  {Y: Set X}
-- given
  (hY: IsTotal Y) :
-- imply
  (∃ x₀ : Y, IsMin x₀) ↔ ∃ x₀, x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x :=
-- proof
  Chapter8.IsMin.iff_lowerbound' hY


-- created on 2026-10-22
