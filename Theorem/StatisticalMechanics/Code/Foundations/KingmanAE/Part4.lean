/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanAE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.Kingman.Part3
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part4
import Def.StatisticalMechanics.Code.Foundations.KingmanAE.Part3
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanAE

open Kingman BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


variable [IsFiniteMeasure μ]


theorem tendsto_div_kingmanLimit_ae (h : SubadditiveCocycle T μ X)
    (heq : ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x)
    (hbot : ∀ᵐ x ∂μ, ⊥ < gStar T X x) :
    ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
  filter_upwards [heq, hbot, gStar_lt_top_ae h] with x hxeq hxbot hxtop
  set ℓ : EReal := gStar T X x with hℓ
  have hlow_le : gStarLow T X x ≤ ℓ := gStarLow_le_gStar x
  have hloweq : liminf (fun n => ((X n x / n : ℝ) : EReal)) atTop = ℓ :=
    le_antisymm hlow_le hxeq
  have hsupeq : limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop = ℓ := rfl
  have htend : Tendsto (fun n => ((X n x / n : ℝ) : EReal)) atTop (𝓝 ℓ) :=
    tendsto_of_liminf_eq_limsup hloweq hsupeq
  have hℓr : ℓ = ((ℓ.toReal : ℝ) : EReal) := (EReal.coe_toReal hxtop.ne hxbot.ne').symm
  rw [hℓr, EReal.tendsto_coe] at htend
  exact htend

omit [IsFiniteMeasure μ] in


theorem limit_le_comp_of_tendsto (h : SubadditiveCocycle T μ X) {ℓ : α → ℝ}
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (ℓ x))) :
    ∀ᵐ x ∂μ, ℓ x ≤ ℓ (T x) := by
  have hconvT : ∀ᵐ x ∂μ, Tendsto (fun n => X n (T x) / n) atTop (𝓝 (ℓ (T x))) :=
    h.measurePreserving.quasiMeasurePreserving.ae hconv
  have hsub : ∀ᵐ x ∂μ, ∀ n, X (n + 1) x ≤ X 1 x + X n (T x) := by
    rw [ae_all_iff]; intro n
    filter_upwards [h.subadditive 1 n] with x hx
    rw [show 1 + n = n + 1 by ring] at hx; simpa using hx
  filter_upwards [hconv, hconvT, hsub] with x hx hxT hxsub
  have hL : Tendsto (fun n => X (n + 1) x / ((n : ℝ) + 1)) atTop (𝓝 (ℓ x)) := by
    have hc := hx.comp (tendsto_add_atTop_nat 1)
    refine hc.congr (fun n => ?_); simp [Function.comp_apply]
  have hR : Tendsto (fun n : ℕ => X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * (X n (T x) / n)) atTop
      (𝓝 (ℓ (T x))) := by
    have h1 : Tendsto (fun n : ℕ => X 1 x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := X 1 x)).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (n + 1) = 1 - 1 / ((n : ℝ) + 1) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp; ring
      rw [tendsto_congr' key]
      have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
    have hsum := h1.add (h2.mul hxT)
    simpa using hsum
  have hle : (fun n => X (n + 1) x / ((n : ℝ) + 1)) ≤ᶠ[atTop]
      (fun n : ℕ => X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * (X n (T x) / n)) := by
    filter_upwards [eventually_gt_atTop 0] with n hpos
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hXle : X (n + 1) x ≤ X 1 x + X n (T x) := hxsub n
    rw [show ((n : ℝ) / (n + 1)) * (X n (T x) / n) = X n (T x) / (n + 1) by field_simp,
        ← add_div, div_le_div_iff_of_pos_right hn1]
    linarith
  exact le_of_tendsto_of_tendsto hL hR hle


theorem kingmanLimit_comp_ae (h : SubadditiveCocycle T μ X)
    (heq : ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x)
    (hbot : ∀ᵐ x ∂μ, ⊥ < gStar T X x)
    (hint : Integrable (kingmanLimit T X) μ) :
    ∀ᵐ x ∂μ, kingmanLimit T X (T x) = kingmanLimit T X x := by
  have hconv := tendsto_div_kingmanLimit_ae h heq hbot
  have hsub : ∀ᵐ x ∂μ, kingmanLimit T X x ≤ kingmanLimit T X (T x) :=
    limit_le_comp_of_tendsto h hconv
  
  set ℓ := kingmanLimit T X with hℓ
  have hintT : Integrable (fun x => ℓ (T x)) μ :=
    h.measurePreserving.integrable_comp_of_integrable hint
  have hge : 0 ≤ᵐ[μ] (fun x => ℓ (T x) - ℓ x) := by
    filter_upwards [hsub] with x hx; simp only [Pi.zero_apply]; linarith
  have heqint : ∫ x, ℓ (T x) ∂μ = ∫ x, ℓ x ∂μ :=
    Kingman.integral_comp_measurePreserving T h.measurePreserving ℓ hint.aestronglyMeasurable
  have hz : ∫ x, (ℓ (T x) - ℓ x) ∂μ = 0 := by
    rw [integral_sub hintT hint, heqint, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hge (hintT.sub hint)).mp hz
  filter_upwards [hae] with x hx
  simp only [Pi.zero_apply] at hx
  linarith


omit [IsFiniteMeasure μ] in

theorem aemeasurable_gStar (h : SubadditiveCocycle T μ X) : AEMeasurable (gStar T X) μ := by
  have hA : ∀ n, AEMeasurable (fun x => ((X n x / n : ℝ) : EReal)) μ := fun n =>
    measurable_coe_real_ereal.comp_aemeasurable
      ((h.integrable n).aestronglyMeasurable.aemeasurable.div_const _)
  refine ⟨fun x => limsup (fun n => (hA n).mk _ x) atTop,
    Measurable.limsup (fun n => (hA n).measurable_mk), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, ((X n x / n : ℝ) : EReal) = (hA n).mk _ x := by
    rw [ae_all_iff]; exact fun n => (hA n).ae_eq_mk
  filter_upwards [hall] with x hx
  unfold gStar
  exact limsup_congr (Eventually.of_forall fun n => hx n)

omit [IsFiniteMeasure μ] in

theorem aemeasurable_kingmanLimit (h : SubadditiveCocycle T μ X) :
    AEMeasurable (kingmanLimit T X) μ :=
  (aemeasurable_gStar h).ereal_toReal

omit [IsFiniteMeasure μ] in

theorem gStar_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] X n) : ∀ᵐ x ∂μ, (0 : EReal) ≤ gStar T X x := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ X n x := by rw [ae_all_iff]; exact hnn
  filter_upwards [hall] with x hx
  unfold gStar
  refine le_limsup_of_frequently_le (Frequently.of_forall (fun n => ?_)) (by isBoundedDefault)
  have hnn' : (0 : ℝ) ≤ X n x / n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · exact div_nonneg (hx n) (by positivity)
  exact_mod_cast hnn'

omit [IsFiniteMeasure μ] in

theorem kingmanLimit_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, 0 ≤ kingmanLimit T X x := by
  filter_upwards [gStar_nonneg_ae (T := T) hnn] with x hx
  exact EReal.toReal_nonneg hx


theorem kingmanLimit_le_birkhoffLimit_ae (h : SubadditiveCocycle T μ X)
    (hnn : ∀ n, 0 ≤ᵐ[μ] X n) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ x ∂μ, kingmanLimit T X x ≤ birkhoffLimit (T^[k]) (X k) x / k := by
  filter_upwards [gStar_le h hk, gStar_nonneg_ae (T := T) hnn] with x hx hg0
  have hbot : gStar T X x ≠ ⊥ := (lt_of_lt_of_le EReal.bot_lt_zero hg0).ne'
  have htop : ((birkhoffLimit (T^[k]) (X k) x / k : ℝ) : EReal) ≠ ⊤ := by simp
  have hmono := EReal.toReal_le_toReal hx hbot htop
  simpa [kingmanLimit] using hmono


theorem integrable_kingmanLimit (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    Integrable (kingmanLimit T X) μ := by
  have hTk : MeasurePreserving (T^[1]) μ μ := h.measurePreserving.iterate 1
  have hB : Integrable (fun x => birkhoffLimit (T^[1]) (X 1) x / 1) μ :=
    (integrable_birkhoffLimit hTk (h.integrable 1)).div_const (1 : ℝ)
  refine Integrable.mono' hB (aemeasurable_kingmanLimit h).aestronglyMeasurable ?_
  filter_upwards [kingmanLimit_nonneg_ae (T := T) hnn,
    kingmanLimit_le_birkhoffLimit_ae h hnn (k := 1) le_rfl] with x hpos hub
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  simpa using hub


theorem integral_birkhoffLimit_block (h : SubadditiveCocycle T μ X) (k : ℕ) :
    ∫ x, birkhoffLimit (T^[k]) (X k) x ∂μ = ∫ x, X k x ∂μ := by
  have hTk : MeasurePreserving (T^[k]) μ μ := h.measurePreserving.iterate k
  have hinv : IsInvariantSet (T^[k]) Set.univ := fun x => by simp
  simpa using (setIntegral_birkhoffLimit hTk (h.integrable k) MeasurableSet.univ hinv).symm


theorem integral_kingmanLimit_le_div (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
    {k : ℕ} (hk : 1 ≤ k) :
    (∫ x, kingmanLimit T X x ∂μ) ≤ (∫ x, X k x ∂μ) / k := by
  have hTk : MeasurePreserving (T^[k]) μ μ := h.measurePreserving.iterate k
  have hBint : Integrable (fun x => birkhoffLimit (T^[k]) (X k) x) μ :=
    integrable_birkhoffLimit hTk (h.integrable k)
  calc (∫ x, kingmanLimit T X x ∂μ)
      ≤ ∫ x, birkhoffLimit (T^[k]) (X k) x / k ∂μ :=
        integral_mono_ae (integrable_kingmanLimit h hnn) (hBint.div_const k)
          (kingmanLimit_le_birkhoffLimit_ae h hnn hk)
    _ = (∫ x, birkhoffLimit (T^[k]) (X k) x ∂μ) / k := integral_div _ _
    _ = (∫ x, X k x ∂μ) / k := by rw [integral_birkhoffLimit_block h k]


theorem integral_kingmanLimit_le_gamma (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    (∫ x, kingmanLimit T X x ∂μ) ≤ SubadditiveCocycle.gamma h := by
  unfold SubadditiveCocycle.gamma Subadditive.lim
  refine le_csInf ⟨SubadditiveCocycle.expSeq X μ 1 / 1, ⟨1, by simp⟩⟩ ?_
  rintro b ⟨n, hn, rfl⟩
  exact integral_kingmanLimit_le_div h hnn hn

end KingmanAE
end StatMech
