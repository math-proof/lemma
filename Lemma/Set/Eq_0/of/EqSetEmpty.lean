import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[α_length_of_empty](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {α: ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (hI: (I:Set ℝ) = ∅) :
-- imply
  α[I]ₗ = 0 :=
-- proof
  Chapter11.α_length_of_empty α hI


-- created on 2026-10-22
