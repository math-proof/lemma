import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open Pointwise


/--
[Jordan_outer_measure_prod_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {E₁: Set (EuclideanSpace' d₁)}
  {E₂: Set (EuclideanSpace' d₂)}
-- given
  (hE₁: JordanMeasurable E₁)
  (hE₂: JordanMeasurable E₂) :
-- imply
  Jordan_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ hE₁.measure * hE₂.measure :=
-- proof
  Jordan_outer_measure_prod_le hE₁ hE₂


-- created on 2026-10-22
