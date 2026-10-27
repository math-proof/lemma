import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open IsElementary


/--
[IsElementary.symmDiff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E)
  (hF: IsElementary F) :
-- imply
  IsElementary (symmDiff E F) :=
-- proof
  IsElementary.symmDiff hE hF


-- created on 2026-10-22
