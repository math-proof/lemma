import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open Pointwise
open JordanMeasurable


/--
[JordanMeasurable.measure_of_prod](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
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
  (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure :=
-- proof
  JordanMeasurable.measure_of_prod hE₁ hE₂


-- created on 2026-10-22
