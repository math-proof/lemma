/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
import Def.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part4
open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


variable [IsFiniteMeasure μ]


theorem tendsto_birkhoffAverage_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (birkhoffLimit T f x)) := by
  filter_upwards [fStarLow_ae_eq_fStar hT hf, fStar_lt_top_ae hT hf, fStarLow_bot_lt_ae hT hf]
    with x heq htop hbot
  
  set ℓ : EReal := fStar T f x with hℓ
  have hlow_eq : liminf (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop = ℓ := heq
  have hsup_eq : limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop = ℓ := rfl
  have htend : Tendsto (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop (𝓝 ℓ) :=
    tendsto_of_liminf_eq_limsup hlow_eq hsup_eq
  have hbot' : (⊥ : EReal) < ℓ := hbot.trans_eq heq
  have hℓr : ℓ = ((ℓ.toReal : ℝ) : EReal) := (EReal.coe_toReal htop.ne hbot'.ne').symm
  rw [hℓr, EReal.tendsto_coe] at htend
  exact htend

omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem birkhoffLimit_comp (x : α) : birkhoffLimit T f (T x) = birkhoffLimit T f x := by
  unfold birkhoffLimit; rw [fStar_comp]

omit [IsFiniteMeasure μ] in

theorem aemeasurable_birkhoffLimit (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    AEMeasurable (birkhoffLimit T f) μ :=
  (aemeasurable_fStar hT hf).ereal_toReal


omit [IsFiniteMeasure μ] in


theorem eLpNorm_birkhoffAverage_le (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    eLpNorm (fun x => birkhoffAverage ℝ T f n x) 1 μ ≤ eLpNorm f 1 μ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [birkhoffAverage_zero']
  have hfm : ∀ k, AEStronglyMeasurable (fun x => f (T^[k] x)) μ := by
    intro k
    rw [← memLp_one_iff_integrable] at hf
    exact (hf.comp_measurePreserving (hT.iterate k)).aestronglyMeasurable
  have hsum : eLpNorm (fun x => ∑ k ∈ range n, f (T^[k] x)) 1 μ ≤ (n : ℝ≥0∞) * eLpNorm f 1 μ := by
    have hle := eLpNorm_sum_le (μ := μ) (p := 1) (f := fun k => fun x => f (T^[k] x))
      (s := range n) (le_refl 1)
    have heq1 : (∑ i ∈ range n, (fun k (x : α) => f (T^[k] x)) i)
        = (fun x => ∑ k ∈ range n, f (T^[k] x)) := by funext x; rw [Finset.sum_apply]
    rw [heq1] at hle
    refine hle.trans ?_
    have hcomp : ∑ k ∈ range n, eLpNorm (fun x => f (T^[k] x)) 1 μ
        = ∑ _k ∈ range n, eLpNorm f 1 μ := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (hT.iterate k)
    rw [hcomp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hAdef : (fun x => birkhoffAverage ℝ T f n x)
      = (n : ℝ)⁻¹ • (fun x => ∑ k ∈ range n, f (T^[k] x)) := by
    funext x; simp [birkhoffAverage, birkhoffSum, Pi.smul_apply]
  rw [hAdef]
  calc eLpNorm ((n : ℝ)⁻¹ • fun x => ∑ k ∈ range n, f (T^[k] x)) 1 μ
      ≤ ‖(n : ℝ)⁻¹‖ₑ * eLpNorm (fun x => ∑ k ∈ range n, f (T^[k] x)) 1 μ := eLpNorm_const_smul_le
    _ ≤ ‖(n : ℝ)⁻¹‖ₑ * ((n : ℝ≥0∞) * eLpNorm f 1 μ) := by gcongr
    _ = eLpNorm f 1 μ := by
        rw [← mul_assoc]
        have h1 : ‖(n : ℝ)⁻¹‖ₑ * (n : ℝ≥0∞) = 1 := by
          rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn),
            ENNReal.ofReal_natCast]
          exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)
        rw [h1, one_mul]


theorem integrable_birkhoffLimit (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    Integrable (birkhoffLimit T f) μ := by
  rw [← memLp_one_iff_integrable]
  have hbound : eLpNorm (birkhoffLimit T f) 1 μ ≤ eLpNorm f 1 μ :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (μ := μ) (p := 1) (C := eLpNorm f 1 μ)
      (Eventually.of_forall fun n => eLpNorm_birkhoffAverage_le hT hf n)
      (fun n => aestronglyMeasurable_birkhoffAverage hT hf n)
      (aemeasurable_birkhoffLimit hT hf).aestronglyMeasurable
      (tendsto_birkhoffAverage_ae hT hf)
  exact lt_of_le_of_lt hbound (memLp_one_iff_integrable.mpr hf)


omit [MeasurableSpace α] [IsFiniteMeasure μ] in


theorem birkhoffAverage_sub_birkhoffLimit (n : ℕ) (hn : 1 ≤ n) (x : α) :
    birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x
      = birkhoffAverage ℝ T f n x - birkhoffLimit T f x := by
  have hLinv : (birkhoffLimit T f) ∘ T = birkhoffLimit T f := by
    funext y; exact birkhoffLimit_comp y
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [show (fun y => f y - birkhoffLimit T f y) = f - birkhoffLimit T f from rfl,
    birkhoffAverage_sub, Pi.sub_apply, birkhoffAverage_of_comp_eq ℝ hLinv hn0]
  rfl


theorem tendsto_birkhoffAverage_sub_birkhoffLimit_ae (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x)
      atTop (𝓝 0) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT hf] with x hx
  have heq : ∀ᶠ n in atTop,
      birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x
        = birkhoffAverage ℝ T f n x - birkhoffLimit T f x := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact birkhoffAverage_sub_birkhoffLimit n hn x
  rw [tendsto_congr' heq]
  have := hx.sub (tendsto_const_nhds (x := birkhoffLimit T f x))
  rwa [sub_self] at this


theorem fStar_sub_birkhoffLimit_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, fStar T (fun y => f y - birkhoffLimit T f y) x = 0 := by
  filter_upwards [tendsto_birkhoffAverage_sub_birkhoffLimit_ae hT hf] with x hx
  unfold fStar
  have hxe : Tendsto
      (fun n => ((birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x : ℝ) : EReal))
      atTop (𝓝 ((0 : ℝ) : EReal)) := by
    rw [EReal.tendsto_coe]; exact hx
  rw [hxe.limsup_eq]; rfl


theorem fStarLow_sub_birkhoffLimit_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, fStarLow T (fun y => f y - birkhoffLimit T f y) x = 0 := by
  filter_upwards [tendsto_birkhoffAverage_sub_birkhoffLimit_ae hT hf] with x hx
  unfold fStarLow
  have hxe : Tendsto
      (fun n => ((birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x : ℝ) : EReal))
      atTop (𝓝 ((0 : ℝ) : EReal)) := by
    rw [EReal.tendsto_coe]; exact hx
  rw [hxe.liminf_eq]; rfl

omit [IsFiniteMeasure μ] in

theorem ae_mem_setOf_fStarLow_lt {g : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hg0 : ∀ᵐ x ∂μ, fStarLow T g x = 0) : ∀ᵐ x ∂μ, fStarLow T g x < (c : EReal) := by
  filter_upwards [hg0] with x hx
  rw [hx]; exact_mod_cast hc

omit [IsFiniteMeasure μ] in

theorem ae_mem_setOf_lt_fStar {g : α → ℝ} {c : ℝ} (hc : c < 0)
    (hg0 : ∀ᵐ x ∂μ, fStar T g x = 0) : ∀ᵐ x ∂μ, (c : EReal) < fStar T g x := by
  filter_upwards [hg0] with x hx
  rw [hx]; exact_mod_cast hc


theorem setIntegral_birkhoffLimit (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) {E : Set α}
    (hEmeas : MeasurableSet E) (hEinv : IsInvariantSet T E) :
    ∫ x in E, f x ∂μ = ∫ x in E, birkhoffLimit T f x ∂μ := by
  set L := birkhoffLimit T f with hL
  set h : α → ℝ := fun y => f y - L y with hh
  have hLint : Integrable L μ := integrable_birkhoffLimit hT hf
  have hhint : Integrable h μ := hf.sub hLint
  have hlow0 : ∀ᵐ x ∂μ, fStarLow T h x = 0 := fStarLow_sub_birkhoffLimit_ae hT hf
  have hsup0 : ∀ᵐ x ∂μ, fStar T h x = 0 := fStar_sub_birkhoffLimit_ae hT hf
  have hEmeas₀ : NullMeasurableSet E μ := hEmeas.nullMeasurableSet
  
  suffices hzero : ∫ x in E, h x ∂μ = 0 by
    have hsplit : ∫ x in E, h x ∂μ = (∫ x in E, f x ∂μ) - ∫ x in E, L x ∂μ := by
      rw [hh]; exact integral_sub hf.integrableOn hLint.integrableOn
    rw [hsplit] at hzero; linarith [hzero]
  
  have hupper : ∀ ε : ℝ, 0 < ε → ∫ x in E, h x ∂μ ≤ ε * (μ E).toReal := by
    intro ε hε
    set S := E ∩ {x | fStarLow T h x < (ε : EReal)} with hS
    have hSinv : IsInvariantSet T S := by
      intro x; simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq, fStarLow_comp, hEinv x]
    have hSmeas : NullMeasurableSet S μ :=
      hEmeas₀.inter (nullMeasurableSet_lt (aemeasurable_fStarLow hT hhint) aemeasurable_const)
    have hSeq : S =ᵐ[μ] E := by
      rw [hS, Filter.eventuallyEq_set]
      filter_upwards [ae_mem_setOf_fStarLow_lt hε hlow0] with x hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hx, and_true]
    calc ∫ x in E, h x ∂μ = ∫ x in S, h x ∂μ := (setIntegral_congr_set hSeq).symm
      _ ≤ ε * (μ S).toReal :=
          setIntegral_le_of_fStarLow_lt hT hhint hSmeas hSinv (fun x hx => hx.2)
      _ = ε * (μ E).toReal := by rw [measure_congr hSeq]
  have hlower : ∀ ε : ℝ, 0 < ε → -(ε * (μ E).toReal) ≤ ∫ x in E, h x ∂μ := by
    intro ε hε
    set S := E ∩ {x | ((-ε : ℝ) : EReal) < fStar T h x} with hS
    have hSinv : IsInvariantSet T S := by
      intro x; simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq, fStar_comp, hEinv x]
    have hSmeas : NullMeasurableSet S μ :=
      hEmeas₀.inter (nullMeasurableSet_lt aemeasurable_const (aemeasurable_fStar hT hhint))
    have hSeq : S =ᵐ[μ] E := by
      rw [hS, Filter.eventuallyEq_set]
      filter_upwards [ae_mem_setOf_lt_fStar (show (-ε : ℝ) < 0 by linarith) hsup0] with x hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hx, and_true]
    calc -(ε * (μ E).toReal) = (-ε) * (μ S).toReal := by rw [measure_congr hSeq]; ring
      _ ≤ ∫ x in S, h x ∂μ :=
          setIntegral_ge_of_lt_fStar hT hhint hSmeas hSinv (fun x hx => hx.2)
      _ = ∫ x in E, h x ∂μ := setIntegral_congr_set hSeq
  
  have hmnn : 0 ≤ (μ E).toReal := ENNReal.toReal_nonneg
  by_contra hne
  set I := ∫ x in E, h x ∂μ with hI
  have habs : 0 < |I| := abs_pos.mpr hne
  
  rcases eq_or_lt_of_le hmnn with hm0 | hmpos
  · 
    have h1 := hupper 1 one_pos
    have h2 := hlower 1 one_pos
    rw [← hm0] at h1 h2; simp at h1 h2; exact hne (le_antisymm h1 h2)
  · 
    set ε := |I| / (2 * (μ E).toReal) with hε
    have hεpos : 0 < ε := by positivity
    have h1 := hupper ε hεpos
    have h2 := hlower ε hεpos
    
    have hcancel : ε * (μ E).toReal = |I| / 2 := by
      rw [hε]; field_simp
    rw [hcancel] at h1 h2
    rcases abs_cases I with ⟨hIabs, _⟩ | ⟨hIabs, _⟩ <;> nlinarith [habs]


omit [IsFiniteMeasure μ] in

theorem measurable_birkhoffAverage (hT : Measurable T) {f₀ : α → ℝ} (hf₀ : Measurable f₀) (n : ℕ) :
    Measurable (fun x => birkhoffAverage ℝ T f₀ n x) := by
  have hbs : Measurable (fun x => birkhoffSum T f₀ n x) := by
    simp only [birkhoffSum]
    exact Finset.measurable_sum _ (fun k _ => hf₀.comp (hT.iterate k))
  simp only [birkhoffAverage, smul_eq_mul]
  exact (measurable_const.mul hbs)

omit [IsFiniteMeasure μ] in

theorem measurable_fStar (hT : Measurable T) {f₀ : α → ℝ} (hf₀ : Measurable f₀) :
    Measurable (fStar T f₀) := by
  unfold fStar
  exact Measurable.limsup (fun n =>
    measurable_coe_real_ereal.comp (measurable_birkhoffAverage hT hf₀ n))

omit [IsFiniteMeasure μ] in


theorem measurable_invariants_birkhoffLimit (hT : Measurable T) {f₀ : α → ℝ} (hf₀ : Measurable f₀) :
    Measurable[MeasurableSpace.invariants T] (birkhoffLimit T f₀) := by
  have hcomp : (fStar T f₀) ∘ T = fStar T f₀ := by funext x; exact fStar_comp x
  have hfStar_inv : Measurable[MeasurableSpace.invariants T] (fStar T f₀) := by
    rw [MeasurableSpace.measurable_invariants_dom]
    refine ⟨measurable_fStar hT hf₀, fun s _ => ?_⟩
    rw [hcomp]
  exact measurable_ereal_toReal.comp hfStar_inv


theorem birkhoffLimit_ae_eq_condExp (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    birkhoffLimit T f =ᵐ[μ] μ[f | MeasurableSpace.invariants T] := by
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace α› := MeasurableSpace.invariants_le T
  
  have hsf : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  
  set f₀ : α → ℝ := hf.1.mk f with hf₀_def
  have hf₀_meas : Measurable f₀ := hf.1.stronglyMeasurable_mk.measurable
  have hff₀ : f =ᵐ[μ] f₀ := hf.1.ae_eq_mk
  have hf₀_int : Integrable f₀ μ := hf.congr hff₀
  
  have hqmp : Measure.QuasiMeasurePreserving T μ μ := hT.quasiMeasurePreserving
  have hLeq : birkhoffLimit T f =ᵐ[μ] birkhoffLimit T f₀ := by
    have hAeq : ∀ᵐ x ∂μ, ∀ n, birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T f₀ n x := by
      rw [ae_all_iff]
      exact fun n => Measure.QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hqmp hff₀ n
    filter_upwards [hAeq] with x hx
    unfold birkhoffLimit fStar
    congr 1
    exact limsup_congr (Eventually.of_forall fun n => by rw [hx n])
  
  have hgm : AEStronglyMeasurable[MeasurableSpace.invariants T] (birkhoffLimit T f) μ :=
    AEStronglyMeasurable.congr
      (measurable_invariants_birkhoffLimit hT.measurable hf₀_meas).stronglyMeasurable.aestronglyMeasurable
      hLeq.symm
  
  have hgeq : ∀ s : Set α, MeasurableSet[MeasurableSpace.invariants T] s → μ s < ∞ →
      ∫ x in s, birkhoffLimit T f x ∂μ = ∫ x in s, f x ∂μ := by
    intro s hs _
    obtain ⟨hs_meas, hs_inv⟩ := (MeasurableSpace.measurableSet_invariants).mp hs
    have hs_invset : IsInvariantSet T s := fun x => by
      constructor
      · intro hx; rw [← hs_inv] at hx; exact hx
      · intro hx; rw [← hs_inv]; exact hx
    exact (setIntegral_birkhoffLimit hT hf hs_meas hs_invset).symm
  
  exact ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun s _ _ => (integrable_birkhoffLimit hT hf).integrableOn)
    (fun s hs hμs => hgeq s hs hμs) hgm


theorem tendsto_birkhoffAverage_condExp_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop
      (𝓝 ((μ[f | MeasurableSpace.invariants T]) x)) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT hf, birkhoffLimit_ae_eq_condExp hT hf]
    with x hx hxeq
  rwa [hxeq] at hx

end BirkhoffAE
end StatMech
