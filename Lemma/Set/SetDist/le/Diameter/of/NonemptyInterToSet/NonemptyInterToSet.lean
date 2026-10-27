import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[diameter_ge_dist_of_intersects](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {E F : Set (EuclideanSpace' d)}
-- given
  (hE : (B.toSet ∩ E).Nonempty)
  (hF : (B.toSet ∩ F).Nonempty) :
-- imply
  set_dist E F ≤ B.diameter :=
-- proof
  Box.diameter_ge_dist_of_intersects B E F hE hF


-- created on 2026-10-22
