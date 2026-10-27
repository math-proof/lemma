import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory


namespace MathlibExt.Probability.Statistics.NeymanPearson

/--
[integrable_val_mul_density](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Statistics/NeymanPearson.lean)
-/
@[path]
integrable. -/
private lemma integrable_val_mul_density {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {w d : Ω → ℝ} (hw : Measurable w)
  (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
  (hd_meas : Measurable d) (hd_nonneg : ∀ x, 0 ≤ d x)
  (hd_int : Integrable d μ) : Integrable (fun x => w x * d x) μ := by
  refine hd_int.mono' (hw.mul hd_meas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hn : ‖w x‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨le_trans (by norm_num) (hw0 x), hw1 x⟩
  calc ‖w x * d x‖ = ‖w x‖ * ‖d x‖ := norm_mul _ _
    _ ≤ 1 * ‖d x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = d x := by rw [one_mul, Real.norm_of_nonneg (hd_nonneg x)]

end MathlibExt.Probability.Statistics.NeymanPearson

namespace MathlibExt.Probability.Statistics.NeymanPearson

/--
[neyman_pearson_dominated_two_simple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Statistics/NeymanPearson.lean)
-/
@[path]
lemma neyman_pearson_dominated_two_simple
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {p q : Ω → ℝ}
  {k : ℝ}
  {φstar : Ω → Set.Icc (0 : ℝ) 1}
-- given
  (hp_meas : Measurable p)
  (hq_meas : Measurable q)
  (hp_nonneg : ∀ x, 0 ≤ p x)
  (hq_nonneg : ∀ x, 0 ≤ q x)
  (hp_int : Integrable p μ)
  (hq_int : Integrable q μ)
  (hk : 0 ≤ k)
  (hφstar_meas : Measurable φstar)
  (hφstar_gt : ∀ x, k * p x < q x → (φstar x).val = 1)
  (hφstar_lt : ∀ x, q x < k * p x → (φstar x).val = 0) :
-- imply
  ∀ (φ : Ω → Set.Icc (0 : ℝ) 1), Measurable φ →
    (∫ x, (φ x).val * p x ∂μ ≤ ∫ x, (φstar x).val * p x ∂μ) →
    (∫ x, (φ x).val * q x ∂μ ≤ ∫ x, (φstar x).val * q x ∂μ) := by
-- proof
  intro φ hφ_meas hsize
  have hstar : Measurable (fun x => (φstar x).val) := hφstar_meas.subtype_val
  have hval : Measurable (fun x => (φ x).val) := hφ_meas.subtype_val
  have hs0 : ∀ x, 0 ≤ (φstar x).val := fun x => (φstar x).property.1
  have hs1 : ∀ x, (φstar x).val ≤ 1 := fun x => (φstar x).property.2
  have hv0 : ∀ x, 0 ≤ (φ x).val := fun x => (φ x).property.1
  have hv1 : ∀ x, (φ x).val ≤ 1 := fun x => (φ x).property.2
  have hint_star_p : Integrable (fun x => (φstar x).val * p x) μ :=
    integrable_val_mul_density hstar hs0 hs1 hp_meas hp_nonneg hp_int
  have hint_val_p : Integrable (fun x => (φ x).val * p x) μ :=
    integrable_val_mul_density hval hv0 hv1 hp_meas hp_nonneg hp_int
  have hint_star_q : Integrable (fun x => (φstar x).val * q x) μ :=
    integrable_val_mul_density hstar hs0 hs1 hq_meas hq_nonneg hq_int
  have hint_val_q : Integrable (fun x => (φ x).val * q x) μ :=
    integrable_val_mul_density hval hv0 hv1 hq_meas hq_nonneg hq_int
  have hint_diff_p : Integrable (fun x => ((φstar x).val - (φ x).val) * p x) μ := by
    apply (hint_star_p.sub hint_val_p).congr
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring
  have hint_diff_q : Integrable (fun x => ((φstar x).val - (φ x).val) * q x) μ := by
    apply (hint_star_q.sub hint_val_q).congr
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring
  have hkey : ∀ x, 0 ≤ ((φstar x).val - (φ x).val) * (q x - k * p x) := by
    intro x
    obtain hlt | heq | hgt := lt_trichotomy (q x) (k * p x)
    · have h0 : (φstar x).val = 0 := hφstar_lt x hlt
      have hφ0 : (0 : ℝ) ≤ (φ x).val := (φ x).property.1
      have hd : (φstar x).val - (φ x).val ≤ 0 := by
        rw [h0]
        exact sub_nonpos.mpr hφ0
      have hqk : q x - k * p x ≤ 0 := sub_nonpos.mpr (le_of_lt hlt)
      exact mul_nonneg_of_nonpos_of_nonpos hd hqk
    · rw [sub_eq_zero.mpr heq, mul_zero]
    · have h1 : (φstar x).val = 1 := hφstar_gt x hgt
      have hφ1 : (φ x).val ≤ 1 := (φ x).property.2
      have hd : (0 : ℝ) ≤ (φstar x).val - (φ x).val := by
        rw [h1]
        exact sub_nonneg.mpr hφ1
      have hqk : (0 : ℝ) ≤ q x - k * p x := sub_nonneg.mpr (le_of_lt hgt)
      exact mul_nonneg hd hqk
  have hint_kdiff_p :
    Integrable (fun x => k * (((φstar x).val - (φ x).val) * p x)) μ :=
    hint_diff_p.const_mul k
  have hG : (∫ x, ((φstar x).val - (φ x).val) * (q x - k * p x) ∂μ)
    = (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ)
      - k * (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ) := by
    have hcongr : (∫ x, ((φstar x).val - (φ x).val) * (q x - k * p x) ∂μ)
      = (∫ x, (((φstar x).val - (φ x).val) * q x
        - k * (((φstar x).val - (φ x).val) * p x)) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    rw [hcongr, integral_sub hint_diff_q hint_kdiff_p, integral_const_mul]
  have hFp : (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ)
    = (∫ x, (φstar x).val * p x ∂μ) - (∫ x, (φ x).val * p x ∂μ) := by
    have hcongr : (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ)
      = (∫ x, ((φstar x).val * p x - (φ x).val * p x) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    rw [hcongr, integral_sub hint_star_p hint_val_p]
  have hFq : (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ)
    = (∫ x, (φstar x).val * q x ∂μ) - (∫ x, (φ x).val * q x ∂μ) := by
    have hcongr : (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ)
      = (∫ x, ((φstar x).val * q x - (φ x).val * q x) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    rw [hcongr, integral_sub hint_star_q hint_val_q]
  have hG_nonneg : (0 : ℝ) ≤ (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ)
    - k * (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ) := by
    rw [← hG]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall hkey)
  have hFp_nonneg : (0 : ℝ) ≤ (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ) := by
    rw [hFp]
    exact sub_nonneg.mpr hsize
  have hFq_nonneg : (0 : ℝ) ≤ (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ) :=
    le_trans (mul_nonneg hk hFp_nonneg) (le_of_sub_nonneg hG_nonneg)
  have hfinal : (0 : ℝ) ≤ (∫ x, (φstar x).val * q x ∂μ)
    - (∫ x, (φ x).val * q x ∂μ) := by
    rwa [← hFq]
  exact le_of_sub_nonneg hfinal

end MathlibExt.Probability.Statistics.NeymanPearson


-- created on 2026-10-20
-- updated on 2026-10-26
