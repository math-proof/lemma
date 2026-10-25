/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Def.StatisticalMechanics.Code.Universality.HexBridgeRecon


namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


theorem hexRec_term_of_cut_recon (lam ups : ℕ → ℝ) (v : ℕ)
    (Cut : HexHighestCut hexChiE⁻¹)
    (hD : (∑' d, Cut.wtγ d) = lam (v + 1) - lam v)
    (hB : (∑' b, Cut.wtB b) = ups (v + 1)) :
    lam (v + 1) - lam v ≤ hexChiE⁻¹ * (ups (v + 1)) ^ 2 := by
  have hrb := Cut.recursion_bound (le_of_lt hexChiE_inv_pos)
  rw [hD, hB] at hrb
  exact hrb


theorem hexZ_chi_div_recon (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE⁻¹ * (ups (v + 1)) ^ 2)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable (fun n => c n * hexChiE ^ n))
    (hυemb : Summable (fun n => c n * hexChiE ^ n) → Summable ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  by_cases hτ : ∃ v, 1 ≤ v ∧ 0 < tau v
  · 
    exact hτcol hτ
  · 
    push Not at hτ
    have hτ0 : ∀ v, 1 ≤ v → tau v = 0 := fun v hv =>
      le_antisymm (hτ v hv) (hτnn v)
    have hbd2 : ∀ v, 1 ≤ v → hexCl * lam v + ups v = 1 := by
      intro v hv
      have h := hbdry v hv
      rw [hτ0 v hv, mul_zero, add_zero] at h
      exact h
    
    have hdefect : ∀ v, 1 ≤ v →
        ups v - ups (v + 1) ≤ (hexCl * hexChiE⁻¹) * (ups (v + 1)) ^ 2 := by
      intro v hv
      have e1 := hbd2 v hv
      have e2 := hbd2 (v + 1) (by omega)
      have hr := hrec v hv
      have hmul : hexCl * (lam (v + 1) - lam v) ≤ hexCl * (hexChiE⁻¹ * (ups (v + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_left hr (le_of_lt hexCl_pos)
      nlinarith [hmul, e1, e2]
    have hυmono : ∀ v, 1 ≤ v → ups (v + 1) ≤ ups v := by
      intro v hv
      have e1 := hbd2 v hv
      have e2 := hbd2 (v + 1) (by omega)
      have hmono := hlamMono v hv
      nlinarith [mul_le_mul_of_nonneg_left hmono (le_of_lt hexCl_pos)]
    set C := hexCl * hexChiE⁻¹ with hCdef
    have hCpos : 0 < C := mul_pos hexCl_pos hexChiE_inv_pos
    have hrecip := hex_recip_induction ups C hCpos hυpos hυmono hdefect
    set m := min (ups 1) (1 / C) with hmdef
    have hmpos : 0 < m := lt_min (hυpos 1 le_rfl) (by positivity)
    have hlower : ∀ v, 1 ≤ v → m / v ≤ ups v := by
      intro v hv
      have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
      have huv := hυpos v hv
      have h := hrecip v hv
      rw [div_le_div_iff₀ huv hmpos] at h
      rw [div_le_iff₀ hvpos]
      nlinarith [h]
    have hυdiv : ¬ Summable ups :=
      hex_div_of_lower_bound ups m hmpos hυnn hlower
    intro hZ
    exact hυdiv (hυemb hZ)


theorem hexZ_chi_div_from_geometry_recon (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  have hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE⁻¹ * (ups (v + 1)) ^ 2 :=
    fun v hv => hexRec_term_of_cut_recon lam ups v (Cut v) (hCutD v hv) (hCutB v hv)
  have hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable (fun n => c n * hexChiE ^ n) := by
    intro hex
    have := Eτ.not_summable_of_not_summable (hτdiv hex)
    rw [hEτ] at this
    exact this
  have hυemb : Summable (fun n => c n * hexChiE ^ n) → Summable ups := by
    intro hZ
    rw [← hEυ] at hZ
    have := Eυ.fiberSum_summable hZ
    rw [hEυc] at this
    exact this
  exact hexZ_chi_div_recon c lam tau ups hbdry hrec hlamMono hυpos hυnn hτnn hτcol hυemb


theorem hexHW_two_overcount_pow_factor (x : ℝ) (hx : 0 < x) (g m n : ℕ)
    (hmn : m + n = g + 2) :
    x ^ g = (x ^ 2)⁻¹ * (x ^ m * x ^ n) := by
  rw [← pow_add, hmn, pow_add]
  field_simp


end StatMech.Universality
