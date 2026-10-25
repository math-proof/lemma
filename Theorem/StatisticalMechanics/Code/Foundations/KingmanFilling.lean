/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.Kingman.Part3
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part4
import Theorem.StatisticalMechanics.Code.Foundations.KingmanAE.Part4
import Def.StatisticalMechanics.Code.Foundations.KingmanFilling
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanFilling

open Kingman BirkhoffAE KingmanAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


theorem aemeasurable_gStarLow (h : SubadditiveCocycle T μ X) : AEMeasurable (gStarLow T X) μ := by
  have hA : ∀ n, AEMeasurable (fun x => ((X n x / n : ℝ) : EReal)) μ := fun n =>
    measurable_coe_real_ereal.comp_aemeasurable
      ((h.integrable n).aestronglyMeasurable.aemeasurable.div_const _)
  refine ⟨fun x => liminf (fun n => (hA n).mk _ x) atTop,
    Measurable.liminf (fun n => (hA n).measurable_mk), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, ((X n x / n : ℝ) : EReal) = (hA n).mk _ x := by
    rw [ae_all_iff]; exact fun n => (hA n).ae_eq_mk
  filter_upwards [hall] with x hx
  unfold gStarLow
  exact liminf_congr (Eventually.of_forall fun n => hx n)


theorem aemeasurable_gLow (h : SubadditiveCocycle T μ X) :
    AEMeasurable (gLow T X) μ :=
  (aemeasurable_gStarLow h).ereal_toReal


theorem gStarLow_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, (0 : EReal) ≤ gStarLow T X x := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ X n x := by rw [ae_all_iff]; exact hnn
  filter_upwards [hall] with x hx
  unfold gStarLow
  refine le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (fun n => ?_))
  have hnn' : (0 : ℝ) ≤ X n x / n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · exact div_nonneg (hx n) (by positivity)
  exact_mod_cast hnn'


theorem gLow_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, 0 ≤ gLow T X x := by
  filter_upwards [gStarLow_nonneg_ae (T := T) hnn] with x hx
  exact EReal.toReal_nonneg hx


theorem eq_of_le_toReal_eq {x y : EReal} (hle : x ≤ y) (hxbot : x ≠ ⊥) (hytop : y ≠ ⊤)
    (heq : x.toReal = y.toReal) : x = y := by
  have hxtop : x ≠ ⊤ := fun hh => hytop (top_le_iff.mp (hh ▸ hle))
  have hybot : y ≠ ⊥ := fun hh => hxbot (le_bot_iff.mp (hh ▸ hle))
  rw [← EReal.coe_toReal hxtop hxbot, ← EReal.coe_toReal hytop hybot, heq]


theorem gStarLow_le_comp (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, gStarLow T X x ≤ gStarLow T X (T x) := by
  have hsub : ∀ᵐ x ∂μ, ∀ n, X (n + 1) x ≤ X 1 x + X n (T x) := by
    rw [ae_all_iff]; intro n
    filter_upwards [h.subadditive 1 n] with x hx
    rw [show 1 + n = n + 1 by ring] at hx; simpa using hx
  filter_upwards [hsub] with x hx
  rw [show gStarLow T X (T x) = liminf (fun n => ((X n (T x) / n : ℝ) : EReal)) atTop from rfl,
     le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)]
  intro y hyL
  obtain ⟨z, hyz, hzL⟩ := EReal.lt_iff_exists_real_btwn.mp hyL
  have hzL' : (z : EReal) < liminf (fun n => ((X n x / n : ℝ) : EReal)) atTop := hzL
  have h0 : ∀ᶠ n in atTop, (z : EReal) < ((X n x / n : ℝ) : EReal) :=
    eventually_lt_of_lt_liminf hzL'
  have hev : ∀ᶠ n in atTop, z < X n x / n := by
    filter_upwards [h0] with n hn; exact_mod_cast hn
  have hev1 : ∀ᶠ n in atTop, z < X (n+1) x / ((n:ℝ)+1) := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hev] with n hn
    rwa [Nat.cast_add_one] at hn
  have hr : Tendsto (fun n : ℕ => (((n:ℝ)+1)/n) * z - X 1 x / n) atTop (𝓝 z) := by
    have h1 : Tendsto (fun n : ℕ => ((n:ℝ)+1)/n) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, ((n:ℝ)+1)/n = 1 + 1/(n:ℝ) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : (n:ℝ) ≠ 0 := by positivity
        field_simp
      rw [tendsto_congr' key]
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => X 1 x / (n:ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := X 1 x)).div_atTop tendsto_natCast_atTop_atTop
    simpa using (h1.mul tendsto_const_nhds).sub h2
  rcases eq_or_ne y ⊥ with hyb | hyb
  · subst hyb
    filter_upwards with n
    exact bot_lt_iff_ne_bot.mpr (by simp)
  · have hytop : y ≠ ⊤ := fun hh => by rw [hh] at hyz; exact (not_top_lt hyz)
    have hyeq : (y.toReal : EReal) = y := EReal.coe_toReal hytop hyb
    have hyr : y.toReal < z := by rw [← hyeq] at hyz; exact_mod_cast hyz
    have hrlt : ∀ᶠ n : ℕ in atTop, y.toReal < (((n:ℝ)+1)/n)*z - X 1 x / n :=
      hr.eventually (eventually_gt_nhds hyr)
    filter_upwards [hev1, hrlt, eventually_gt_atTop 0] with n hn1 hn2 hpos
    have hnn : (0:ℝ) < n := by exact_mod_cast hpos
    have hXle : X (n+1) x ≤ X 1 x + X n (T x) := hx n
    have hXn1 : ((n:ℝ)+1) * z < X (n+1) x := by
      rw [lt_div_iff₀ (by positivity)] at hn1; linarith [hn1]
    have hXnT : ((n:ℝ)+1)*z - X 1 x < X n (T x) := by linarith [hXle, hXn1]
    have hgoal : y.toReal < X n (T x) / n := by
      rw [lt_div_iff₀ hnn]
      have hmul : y.toReal * n < ((((n:ℝ)+1)/n)*z - X 1 x/n) * n :=
        mul_lt_mul_of_pos_right hn2 hnn
      have hrhs : ((((n:ℝ)+1)/n)*z - X 1 x/n) * n = ((n:ℝ)+1)*z - X 1 x := by
        field_simp
      rw [hrhs] at hmul; linarith [hXnT, hmul]
    rw [← hyeq]; exact_mod_cast hgoal


end KingmanFilling
end StatMech
