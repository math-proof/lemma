import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_of_disjUnion'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {S: Finset (Set (EuclideanSpace' d))}
-- given
  (hE: ∀ E ∈ S, IsElementary E)
  (hdisj: (S : Set (Set (EuclideanSpace' d))).PairwiseDisjoint id) :
-- imply
  (IsElementary.union' hE).measure = ∑ E:S, (hE E.val E.property).measure :=
-- proof
  IsElementary.measure_of_disjUnion' hE hdisj


-- created on 2026-10-22
