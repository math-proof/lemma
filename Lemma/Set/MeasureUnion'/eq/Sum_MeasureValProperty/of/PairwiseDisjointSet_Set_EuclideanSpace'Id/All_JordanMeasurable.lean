import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open JordanMeasurable


/--
[JordanMeasurable.measure_of_disjUnion'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {S: Finset (Set (EuclideanSpace' d))}
-- given
  (hE: ∀ E ∈ S, JordanMeasurable E)
  (hdisj: (S : Set (Set (EuclideanSpace' d))).PairwiseDisjoint id) :
-- imply
  (JordanMeasurable.union' hE).measure = ∑ E:S, (hE E.val E.property).measure :=
-- proof
  JordanMeasurable.measure_of_disjUnion' hE hdisj


-- created on 2026-10-22
