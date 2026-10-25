import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Lebesgue_outer_measure


/--
[Lebesgue_outer_measure.of_open](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: IsOpen E) :
-- imply
  Lebesgue_outer_measure E = Jordan_inner_measure' E :=
-- proof
  Lebesgue_outer_measure.of_open E hE


-- created on 2026-10-22
