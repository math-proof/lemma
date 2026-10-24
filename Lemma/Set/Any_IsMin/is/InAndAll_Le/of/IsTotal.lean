import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_5
open Chapter8
open Chapter8.IsMin


/--
[IsMin.iff_lowerbound](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  {X:Type} [PartialOrder X]
  {Y: Set X}
  {x₀ : X}
-- given
  (hY: IsTotal Y) :
-- imply
  (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩:Y)) ↔ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x :=
-- proof
  Chapter8.IsMin.iff_lowerbound hY x₀


-- created on 2026-10-22
