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
import Def.StatisticalMechanics.Code.Foundations.KingmanAE
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanAE

open Kingman BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


variable [IsFiniteMeasure μ]


omit [IsFiniteMeasure μ] in

theorem remDom_integrable (h : SubadditiveCocycle T μ X) (k : ℕ) : Integrable (remDom X k) μ := by
  unfold remDom; exact integrable_finsetSum _ (fun r _ => (h.integrable r).pos_part)

omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem remDom_nonneg (X : ℕ → α → ℝ) (k : ℕ) (y : α) : 0 ≤ remDom X k y := by
  unfold remDom; positivity

omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem le_remDom (X : ℕ → α → ℝ) {k r : ℕ} (hr : r < k) (y : α) : X r y ≤ remDom X k y := by
  unfold remDom
  calc X r y ≤ (X r y)⁺ := le_max_left _ _
    _ ≤ ∑ s ∈ Finset.range k, (X s y)⁺ :=
        Finset.single_le_sum (f := fun s => (X s y)⁺) (fun i _ => by positivity)
          (Finset.mem_range.mpr hr)


theorem gStar_le (h : SubadditiveCocycle T μ X) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ x ∂μ, limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop
      ≤ ((birkhoffLimit (T^[k]) (X k) x / k : ℝ) : EReal) := by
  have hTk : MeasurePreserving (T^[k]) μ μ := h.measurePreserving.iterate k
  filter_upwards [ae_all_subadditive h, ae_le_block_birkhoffSum h,
    tendsto_birkhoffAverage_ae hTk (h.integrable k),
    tendsto_comp_div_atTop h.measurePreserving (remDom_integrable h k)] with x hsub hblk hbirk hrem
  set Λ : ℝ := birkhoffLimit (T^[k]) (X k) x with hΛ
  set q : ℕ → ℕ := fun n => n / k with hq
  set R : ℕ → ℝ := fun n =>
    ((q n : ℝ) / n) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x
      + remDom X k (T^[q n * k] x) / (q n * k) with hR
  
  have hle : ∀ᶠ n in atTop, X n x / n ≤ R n := by
    filter_upwards [eventually_ge_atTop k] with n hn
    have hkpos : 0 < k := hk
    have hnpos : 0 < n := lt_of_lt_of_le hkpos hn
    have hqpos : 1 ≤ q n := by rw [hq]; exact (Nat.one_le_div_iff hkpos).mpr hn
    have hqk_pos : 0 < q n * k := Nat.mul_pos hqpos hkpos
    have hqk_le : q n * k ≤ n := by rw [hq]; exact Nat.div_mul_le_self n k
    have hr : n % k < k := Nat.mod_lt n hkpos
    have hdecomp : q n * k + n % k = n := by rw [hq]; exact Nat.div_add_mod' n k
    have hcoc : X n x ≤ X (q n * k) x + X (n % k) (T^[q n * k] x) := by
      have := hsub (q n * k) (n % k); rwa [hdecomp] at this
    have hblock : X (q n * k) x ≤ birkhoffSum (T^[k]) (X k) (q n) x := hblk k (q n) hqpos
    have hremb : X (n % k) (T^[q n * k] x) ≤ remDom X k (T^[q n * k] x) :=
      le_remDom X hr (T^[q n * k] x)
    have hXn : X n x ≤ birkhoffSum (T^[k]) (X k) (q n) x + remDom X k (T^[q n * k] x) :=
      calc X n x ≤ X (q n * k) x + X (n % k) (T^[q n * k] x) := hcoc
        _ ≤ birkhoffSum (T^[k]) (X k) (q n) x + remDom X k (T^[q n * k] x) := by gcongr
    have hbs : birkhoffSum (T^[k]) (X k) (q n) x
        = (q n : ℝ) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x := by
      rw [birkhoffAverage, smul_eq_mul, ← mul_assoc]
      rcases Nat.eq_zero_or_pos (q n) with h0 | h0
      · simp [h0, birkhoffSum_zero]
      · rw [mul_inv_cancel₀ (by exact_mod_cast h0.ne'), one_mul]
    have hremdiv : remDom X k (T^[q n * k] x)
        ≤ remDom X k (T^[q n * k] x) / (q n * k) * n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hqk_pos)]
      have hnn : 0 ≤ remDom X k (T^[q n * k] x) := remDom_nonneg X k _
      have hqkn : (q n * k : ℝ) ≤ n := by exact_mod_cast hqk_le
      nlinarith [hnn, hqkn]
    rw [div_le_iff₀ (by exact_mod_cast hnpos)]
    calc X n x ≤ birkhoffSum (T^[k]) (X k) (q n) x + remDom X k (T^[q n * k] x) := hXn
      _ = (q n : ℝ) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x
            + remDom X k (T^[q n * k] x) := by rw [hbs]
      _ ≤ (q n : ℝ) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x
            + remDom X k (T^[q n * k] x) / (q n * k) * n := by linarith [hremdiv]
      _ = R n * n := by rw [hR]; field_simp
  
  have hRtend : Tendsto R atTop (𝓝 (Λ / k)) := by
    have hqinf : Tendsto q atTop atTop := tendsto_natDiv_atTop hk
    have hratio : Tendsto (fun n : ℕ => ((q n : ℝ)) / (n : ℝ)) atTop (𝓝 (1 / (k : ℝ))) :=
      tendsto_natDiv_div_atTop hk
    have hAcomp : Tendsto (fun n : ℕ => birkhoffAverage ℝ (T^[k]) (X k) (q n) x) atTop (𝓝 Λ) :=
      hbirk.comp hqinf
    have hterm1 : Tendsto
        (fun n : ℕ => ((q n : ℝ) / n) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x) atTop
        (𝓝 (1 / (k : ℝ) * Λ)) := hratio.mul hAcomp
    have hqkinf : Tendsto (fun n : ℕ => q n * k) atTop atTop := by
      have hmk : Tendsto (fun m : ℕ => m * k) atTop atTop := by
        apply tendsto_atTop_atTop.2; intro b; refine ⟨b, fun m hm => ?_⟩
        exact le_trans hm (Nat.le_mul_of_pos_right m hk)
      exact hmk.comp hqinf
    have hterm2 : Tendsto (fun n : ℕ => remDom X k (T^[q n * k] x) / (q n * k)) atTop (𝓝 0) := by
      have hc := hrem.comp hqkinf
      refine hc.congr (fun n => ?_)
      simp only [Function.comp_apply, Nat.cast_mul]
    have hsum := hterm1.add hterm2
    rw [add_zero] at hsum
    have : 1 / (k : ℝ) * Λ = Λ / k := by rw [div_mul_eq_mul_div, one_mul]
    rwa [this] at hsum
  
  have h1 : limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop
      ≤ limsup (fun n => ((R n : ℝ) : EReal)) atTop := by
    refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [hle] with n hn; exact_mod_cast hn
  have h2 : Tendsto (fun n => ((R n : ℝ) : EReal)) atTop (𝓝 ((Λ / k : ℝ) : EReal)) := by
    rw [EReal.tendsto_coe]; exact hRtend
  rw [h2.limsup_eq] at h1
  exact h1


end KingmanAE
end StatMech
