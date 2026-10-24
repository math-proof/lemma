import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_irrelevant](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (h₀ h₁ : IsElementary E) :
-- imply
  h₀.measure = h₁.measure :=
-- proof
  IsElementary.measure_irrelevant h₀ h₁


-- created on 2026-10-22
