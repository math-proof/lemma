import Mathlib
import sympy.Basic
open Set
open scoped ENNReal


namespace MeasureTheory

/--
[exists_gt_not_mem_of_volume_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/Empty.Finite.lean)
-/
@[path]
lemma exists_gt_not_mem_of_volume_lt_top
  {E : Set ℝ}
  {X : ℝ}
-- given
  (hE : volume E < ∞) :
-- imply
  ∃ x : ℝ, X < x ∧ x ∉ E := by
-- proof
  by_contra! h
  have hmono : volume (Ioi X) ≤ volume E := measure_mono fun x hx ↦ h x hx
  have htop : (∞ : ℝ≥0∞) ≤ volume E := by
    simpa only [Real.volume_Ioi] using hmono
  exact (not_lt_of_ge htop) hE

end MeasureTheory


-- created on 2026-10-20
-- updated on 2026-10-23
