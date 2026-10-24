import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2
open Pointwise
open JordanMeasurable


/--
[JordanMeasurable.prod](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
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
  JordanMeasurable (EuclideanSpace'.prod E₁ E₂) :=
-- proof
  JordanMeasurable.prod hE₁ hE₂


-- created on 2026-10-22
