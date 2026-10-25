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
open MeasureTheory Filter Topology


namespace StatMech

namespace KingmanAE

open Kingman BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


theorem ae_all_subadditive (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, ∀ m n, X (m + n) x ≤ X m x + X n (T^[m] x) := by
  rw [ae_all_iff]
  intro m
  rw [ae_all_iff]
  intro n
  exact h.subadditive m n


theorem ae_le_block_birkhoffSum (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, ∀ k q, 1 ≤ q → X (q * k) x ≤ birkhoffSum (T^[k]) (X k) q x := by
  filter_upwards [ae_all_subadditive h] with x hx
  intro k q
  induction q with
  | zero => intro h0; exact absurd h0 (by norm_num)
  | succ q ih =>
    intro _
    have hstep : X ((q + 1) * k) x ≤ X (q * k) x + X k (T^[q * k] x) := by
      have := hx (q * k) k
      rwa [show q * k + k = (q + 1) * k by ring] at this
    have hiter : (T^[k])^[q] x = T^[q * k] x := by
      rw [← Function.iterate_mul, Nat.mul_comm]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp only [Nat.zero_add, Nat.one_mul, birkhoffSum_one, le_refl]
    · calc X ((q + 1) * k) x ≤ X (q * k) x + X k (T^[q * k] x) := hstep
        _ ≤ birkhoffSum (T^[k]) (X k) q x + X k (T^[q * k] x) := by gcongr; exact ih hq
        _ = birkhoffSum (T^[k]) (X k) q x + X k ((T^[k])^[q] x) := by rw [hiter]
        _ = birkhoffSum (T^[k]) (X k) (q + 1) x := (birkhoffSum_succ_apply (T^[k]) (X k) q x).symm


variable [IsFiniteMeasure μ]


theorem tendsto_comp_div_atTop (hT : MeasurePreserving T μ μ) {g : α → ℝ}
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun m : ℕ => g (T^[m] x) / m) atTop (𝓝 0) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT hg] with x hx
  set L : ℝ := birkhoffLimit T g x with hL
  
  have hkey : ∀ᶠ m : ℕ in atTop, g (T^[m] x) / m
      = (((m : ℝ) + 1) / m) * birkhoffAverage ℝ T g (m + 1) x - birkhoffAverage ℝ T g m x := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hsucc : birkhoffSum T g (m + 1) x = birkhoffSum T g m x + g (T^[m] x) :=
      birkhoffSum_succ_apply T g m x
    simp only [birkhoffAverage, smul_eq_mul]
    rw [hsucc]
    push_cast
    field_simp
    ring
  rw [tendsto_congr' hkey]
  
  have hr : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / m) atTop (𝓝 1) := by
    have key : ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 1) / m = 1 + 1 / (m : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with m hm
      have : (m : ℝ) ≠ 0 := by positivity
      field_simp
    rw [tendsto_congr' key]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
  have hA1 : Tendsto (fun m : ℕ => birkhoffAverage ℝ T g (m + 1) x) atTop (𝓝 L) :=
    hx.comp (tendsto_add_atTop_nat 1)
  have hprod : Tendsto (fun m : ℕ => (((m : ℝ) + 1) / m) * birkhoffAverage ℝ T g (m + 1) x)
      atTop (𝓝 (1 * L)) := hr.mul hA1
  rw [one_mul] at hprod
  have := hprod.sub hx
  rwa [sub_self] at this


omit [IsFiniteMeasure μ] in

theorem tendsto_natDiv_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => n / k) atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro b
  refine ⟨b * k, fun n hn => ?_⟩
  calc b = b * k / k := by rw [Nat.mul_div_cancel _ hk]
    _ ≤ n / k := Nat.div_le_div_right hn

omit [IsFiniteMeasure μ] in

theorem tendsto_natDiv_div_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (k : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hupper : ∀ n : ℕ, ((n / k : ℕ) : ℝ) * k / n ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast hn)]
      have hle : (n / k) * k ≤ n := Nat.div_mul_le_self n k
      calc ((n / k : ℕ) : ℝ) * k = (((n / k) * k : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (n : ℝ) := by exact_mod_cast hle
  have hlower : ∀ n : ℕ, 1 ≤ n → 1 - (k : ℝ) / n ≤ ((n / k : ℕ) : ℝ) * k / n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlt : n < (n / k) * k + k := Nat.lt_div_mul_add hk
    have h2 : (n : ℝ) ≤ ((n / k : ℕ) : ℝ) * k + k := by
      calc (n : ℝ) ≤ (((n / k) * k + k : ℕ) : ℝ) := by exact_mod_cast hlt.le
        _ = ((n / k : ℕ) : ℝ) * k + k := by push_cast; ring
    rw [sub_le_iff_le_add,
      show ((n / k : ℕ) : ℝ) * k / n + (k : ℝ) / n = (((n / k : ℕ) : ℝ) * k + k) / n by ring,
      le_div_iff₀ hn0, one_mul]
    exact h2
  have hmid : Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) * k / n) atTop (𝓝 1) := by
    have hL : Tendsto (fun n : ℕ => 1 - (k : ℝ) / n) atTop (𝓝 1) := by
      have hkz : Tendsto (fun n : ℕ => (k : ℝ) / n) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (k : ℝ))).div_atTop tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hkz
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with n hn using hlower n hn
    · filter_upwards with n using hupper n
  have hfin : Tendsto (fun n : ℕ => (((n / k : ℕ) : ℝ) * k / n) / k) atTop (𝓝 (1 / k)) :=
    hmid.div_const k
  refine hfin.congr (fun n => ?_)
  by_cases hn : n = 0
  · simp [hn]
  · field_simp


end KingmanAE
end StatMech
