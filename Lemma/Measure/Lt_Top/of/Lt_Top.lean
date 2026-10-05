import Mathlib
import sympy.Basic

open MeasureTheory

/--
[MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top.lean)
-/
@[main]
private lemma main
  [Group G] [MeasurableSpace G] [MeasurableMul G]
  {μ : Measure G} [μ.IsMulRightInvariant]
  {s : Set G}
  {T : Finset G}
-- given
  (hs : μ s < ⊤) :
-- imply
  μ (⋃ x ∈ T, (· * x) '' s) < ⊤ := by
-- proof
  refine lt_of_le_of_lt (measure_biUnion_finset_le T _) ?_
  refine ENNReal.sum_lt_top.mpr fun x _ => ?_
  have : (· * x) '' s = (· * x⁻¹) ⁻¹' s := by
    ext g; simp [Set.mem_preimage]
  rw [this, measure_preimage_mul_right]
  exact hs


-- created on 2026-10-05
