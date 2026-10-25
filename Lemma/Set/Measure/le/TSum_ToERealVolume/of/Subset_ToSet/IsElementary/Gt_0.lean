import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsElementary


/--
[measure_le_cover_sum](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {E : Set (EuclideanSpace' d)}
  {S : ℕ → Box d}
-- given
  (hd : 0 < d)
  (hE : IsElementary E)
  (hS_cover : E ⊆ ⋃ n, (S n).toSet) :
-- imply
  (hE.measure : EReal) ≤ ∑' n, (S n).volume.toEReal :=
-- proof
  IsElementary.measure_le_cover_sum hd hE S hS_cover


-- created on 2026-10-22
