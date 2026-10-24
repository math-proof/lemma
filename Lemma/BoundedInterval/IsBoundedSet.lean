import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Bornology
open Bornology.IsBounded


/--
[Bornology.IsBounded.of_boundedInterval](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  Bornology.IsBounded (I:Set ℝ) :=
-- proof
  Bornology.IsBounded.of_boundedInterval I


-- created on 2026-10-22
