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
import Def.StatisticalMechanics.Code.Foundations.KingmanAE.Part2
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanAE

open Kingman BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


variable [IsFiniteMeasure μ]


omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem gStarLow_le_gStar (x : α) : gStarLow T X x ≤ gStar T X x := liminf_le_limsup

omit [IsFiniteMeasure μ] in


theorem gStar_le_comp (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, gStar T X x ≤ gStar T X (T x) := by
  have hsub : ∀ᵐ x ∂μ, ∀ n, X (n + 1) x ≤ X 1 x + X n (T x) := by
    rw [ae_all_iff]; intro n
    filter_upwards [h.subadditive 1 n] with x hx
    rw [show 1 + n = n + 1 by ring] at hx; simpa using hx
  filter_upwards [hsub] with x hx
  unfold gStar
  set L : EReal := limsup (fun n => ((X n (T x) / n : ℝ) : EReal)) atTop with hL
  rw [limsup_le_iff']
  intro y hyL
  obtain ⟨z, hLz, hzy⟩ := EReal.lt_iff_exists_real_btwn.mp hyL
  have h0 : ∀ᶠ n in atTop, ((X n (T x) / n : ℝ) : EReal) < (z : EReal) :=
    eventually_lt_of_limsup_lt (hL ▸ hLz)
  have hev : ∀ᶠ n in atTop, X n (T x) / n < z := by
    filter_upwards [h0] with n hn; exact_mod_cast hn
  have hr : Tendsto (fun n : ℕ => X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * z) atTop (𝓝 z) := by
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
    simpa using h1.add (h2.mul tendsto_const_nhds)
  have hbound : ∀ᶠ n in atTop,
      X (n + 1) x / (n + 1) < X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * z := by
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hpos
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hXle : X (n + 1) x ≤ X 1 x + X n (T x) := hx n
    have hXn : X n (T x) < n * z := by rw [div_lt_iff₀ hnn] at hn; linarith [hn]
    have hrw : X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * z = (X 1 x + n * z) / (n + 1) := by
      field_simp
    rw [hrw, div_lt_div_iff_of_pos_right hn1]; linarith
  rcases eq_top_or_lt_top y with hytop | hytop
  · filter_upwards with n; rw [hytop]; exact le_top
  · have hybot : y ≠ ⊥ := fun hh => by rw [hh] at hzy; exact not_lt_bot hzy
    have hyr : y = (y.toReal : EReal) := (EReal.coe_toReal hytop.ne hybot).symm
    have hzyr : z < y.toReal := by rw [hyr] at hzy; exact_mod_cast hzy
    have hrlt : ∀ᶠ n : ℕ in atTop, X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * z < y.toReal :=
      hr.eventually (eventually_lt_nhds hzyr)
    have hsucc : ∀ᶠ n in atTop, ((X (n + 1) x / ((n : ℝ) + 1) : ℝ) : EReal) ≤ y := by
      filter_upwards [hbound, hrlt] with n hn1 hn2
      have hlt : X (n + 1) x / (n + 1) < y.toReal := lt_trans hn1 hn2
      rw [hyr]; exact_mod_cast hlt.le
    rw [eventually_atTop] at hsucc ⊢
    obtain ⟨N, hN⟩ := hsucc
    refine ⟨N + 1, fun m hm => ?_⟩
    have hmm : (m - 1) + 1 = m := by omega
    have key := hN (m - 1) (by omega)
    rw [hmm] at key
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by rw [← hmm]; push_cast; ring
    rw [hcast] at key
    exact key


theorem gStar_le_birkhoffLimit (h : SubadditiveCocycle T μ X) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ x ∂μ, gStar T X x ≤ ((birkhoffLimit (T^[k]) (X k) x / k : ℝ) : EReal) :=
  gStar_le h hk


theorem gStar_lt_top_ae (h : SubadditiveCocycle T μ X) : ∀ᵐ x ∂μ, gStar T X x < ⊤ := by
  filter_upwards [gStar_le h (k := 1) le_rfl] with x hx
  exact lt_of_le_of_lt hx (EReal.coe_lt_top _)


theorem gStar_le_birkhoffLimit_one (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, gStar T X x ≤ ((birkhoffLimit T (X 1) x : ℝ) : EReal) := by
  filter_upwards [gStar_le h (k := 1) le_rfl] with x hx
  simpa using hx


end KingmanAE
end StatMech
