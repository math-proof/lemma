import Mathlib
import sympy.Basic
open MeasureTheory Set Filter Topology intervalIntegral


namespace Integration

/--
[integral_comparison_and_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Properties.lean)
-/
@[path]
lemma integral_comparison_and_triangle
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hf : ContinuousOn f (Set.Icc a b))
  (hg : ContinuousOn g (Set.Icc a b)) :
-- imply
  ((∀ x ∈ Set.Icc a b, f x ≤ g x) → ∫ x in a..b, f x ≤ ∫ x in a..b, g x) ∧ (|∫ x in a..b, f x| ≤ ∫ x in a..b, |f x|) := by
-- proof
  constructor
  · intro hle
    exact intervalIntegral.integral_mono_on hab
      (hf.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable_of_Icc hab) hle
  · have h_norm : ‖∫ x in a..b, f x‖ ≤ ∫ x in a..b, ‖f x‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
    simp only [Real.norm_eq_abs] at h_norm
    exact h_norm

end Integration

namespace Integration

/--
[integral_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Properties.lean)
-/
@[path]
lemma integral_bounds
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hf : ContinuousOn f (Set.Icc a b)) :
-- imply
  (sInf (f '' Set.Icc a b)) * (b - a) ≤ ∫ x in a..b, f x ∧ ∫ x in a..b, f x ≤ (sSup (f '' Set.Icc a b)) * (b - a) := by
-- proof
  have hint : IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hf
  have hcompact : IsCompact (f '' Set.Icc a b) :=
    isCompact_Icc.image_of_continuousOn hf
  have hbdd_above : BddAbove (f '' Set.Icc a b) := hcompact.bddAbove
  have hbdd_below : BddBelow (f '' Set.Icc a b) := hcompact.bddBelow
  constructor
  · calc sInf (f '' Set.Icc a b) * (b - a)
    = ∫ _ in a..b, sInf (f '' Set.Icc a b) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ x in a..b, f x := by
      apply intervalIntegral.integral_mono_on hab
        intervalIntegral.intervalIntegrable_const hint
      intro x hx
      exact csInf_le hbdd_below (Set.mem_image_of_mem f hx)
  · calc ∫ x in a..b, f x
    ≤ ∫ _ in a..b, sSup (f '' Set.Icc a b) := by
      apply intervalIntegral.integral_mono_on hab hint
        intervalIntegral.intervalIntegrable_const
      intro x hx
      exact le_csSup hbdd_above (Set.mem_image_of_mem f hx)
    _ = sSup (f '' Set.Icc a b) * (b - a) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

end Integration

namespace Integration

/--
[integral_additivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Properties.lean)
-/
@[path]
lemma integral_additivity
  {f : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hac : a < c)
  (hcb : c < b)
  (hf : ContinuousOn f (Set.Icc a b)) :
-- imply
  ∫ x in a..b, f x = (∫ x in a..c, f x) + ∫ x in c..b, f x := by
-- proof
  have hac' : a ≤ c := le_of_lt hac
  have hcb' : c ≤ b := le_of_lt hcb
  have hf_ac : ContinuousOn f (Set.Icc a c) :=
    hf.mono (Set.Icc_subset_Icc_right hcb')
  have hf_cb : ContinuousOn f (Set.Icc c b) :=
    hf.mono (Set.Icc_subset_Icc_left hac')
  have hint_ac : IntervalIntegrable f volume a c :=
    ContinuousOn.intervalIntegrable_of_Icc hac' hf_ac
  have hint_cb : IntervalIntegrable f volume c b :=
    ContinuousOn.intervalIntegrable_of_Icc hcb' hf_cb
  exact (integral_add_adjacent_intervals hint_ac hint_cb).symm

end Integration

namespace Integration

/--
[integral_linearity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Properties.lean)
-/
@[path]
lemma integral_linearity
  {f g : ℝ → ℝ}
  {a b α : ℝ}
-- given
  (hf : ContinuousOn f (Set.Icc a b))
  (hg : ContinuousOn g (Set.Icc a b))
  (hab : a ≤ b) :
-- imply
  ∫ x in a..b, (α * f x + g x) = α * (∫ x in a..b, f x) + ∫ x in a..b, g x := by
-- proof
  have hf_int : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have hg_int : IntervalIntegrable g volume a b :=
    hg.intervalIntegrable_of_Icc hab
  have hαf_int : IntervalIntegrable (fun x => α * f x) volume a b :=
    hf_int.const_mul α
  rw [intervalIntegral.integral_add hαf_int hg_int,
    intervalIntegral.integral_const_mul]

end Integration


-- created on 2026-10-23
