import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_of_prod](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {E₁: Set (EuclideanSpace' d₁)}
  {E₂: Set (EuclideanSpace' d₂)}
-- given
  (hE₁: IsElementary E₁)
  (hE₂: IsElementary E₂) :
-- imply
  (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure :=
-- proof
  IsElementary.measure_of_prod hE₁ hE₂


-- created on 2026-10-22
