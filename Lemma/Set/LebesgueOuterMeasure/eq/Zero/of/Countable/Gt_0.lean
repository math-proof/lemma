import Mathlib
import sympy.Basic
import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
open BoundedInterval
open Countable


/--
[Countable.Lebesgue_measure](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hd : 0 < d)
  (hE: E.Countable) :
-- imply
  Lebesgue_outer_measure E = 0 :=
-- proof
  Countable.Lebesgue_measure hd hE


-- created on 2026-10-22
