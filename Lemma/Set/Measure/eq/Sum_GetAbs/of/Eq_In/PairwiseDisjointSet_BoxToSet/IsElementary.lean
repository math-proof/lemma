import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {T: Finset (Box d)}
-- given
  (hE: IsElementary E)
  (hT: (T : Set (Box d)).PairwiseDisjoint Box.toSet)
  (heq : E = ⋃ B ∈ T, B.toSet) :
-- imply
  hE.measure = ∑ B ∈ T, |B|ᵥ :=
-- proof
  IsElementary.measure_eq hE hT heq


-- created on 2026-10-22
