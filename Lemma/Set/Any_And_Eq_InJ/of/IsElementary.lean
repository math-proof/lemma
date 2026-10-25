import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.partition](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E) :
-- imply
  ∃ T: Finset (Box d), (T : Set (Box d)).PairwiseDisjoint Box.toSet ∧ E = ⋃ J ∈ T, J.toSet :=
-- proof
  IsElementary.partition hE


-- created on 2026-10-22
