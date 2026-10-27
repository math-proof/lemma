import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_of_disjUnion](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E)
  (hF: IsElementary F)
  (hdisj: Disjoint E F) :
-- imply
  (hE.union hF).measure = hE.measure + hF.measure :=
-- proof
  IsElementary.measure_of_disjUnion hE hF hdisj


-- created on 2026-10-22
