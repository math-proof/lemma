import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[partition_volume_bound](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {P P_nonempty : Finset (Box d)}
  {hP_nonempty_sub : P_nonempty ⊆ P}
  {B' : (B : Box d) → B ∈ P_nonempty → Box d}
  {ε : ℝ}
-- given
  (hε_pos : 0 < ε)
  (h_vol_bound : ∀ B (hB : B ∈ P_nonempty), B.volume ≤ (B' B hB).volume + ε) :
-- imply
  ∑ B ∈ P_nonempty, B.volume ≤
    ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume + P_nonempty.card * ε :=
-- proof
  partition_volume_bound hP_nonempty_sub hε_pos h_vol_bound


-- created on 2026-10-22
