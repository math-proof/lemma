import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsElementary


/--
[IsElementary.almost_disjoint](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d k:ℕ}
  {E: Set (EuclideanSpace' d)}
  {B: Fin k → Box d}
-- given
  (hE: IsElementary E)
  (hEB: E = ⋃ i, (B i).toSet)
  (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) :
-- imply
  hE.measure = ∑ i, |B i|ᵥ :=
-- proof
  IsElementary.almost_disjoint hE B hEB hdisj


-- created on 2026-10-22
