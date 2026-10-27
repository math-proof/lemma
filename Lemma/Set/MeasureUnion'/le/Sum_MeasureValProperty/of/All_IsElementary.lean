import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_of_union'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {S: Finset (Set (EuclideanSpace' d))}
-- given
  (hE: ∀ E ∈ S, IsElementary E) :
-- imply
  (IsElementary.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure :=
-- proof
  IsElementary.measure_of_union' hE


-- created on 2026-10-22
