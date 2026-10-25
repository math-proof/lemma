/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose.Part2


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal BigOperators


theorem hxf_bdry_combined {Iυ Ila : Type}
    (Eυ : HexColumnEmb ℕ Iυ) (Ela : HexColumnEmb ℕ Ila)
    (tau : ℕ → ℝ)
    (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
    (hτEq : ∀ v, (B v).tau = tau v)
    (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v) :
    ∀ v, 1 ≤ v →
      hexCl * hbr_lamCum (Ela.fiberSum) v + hexCt * tau v + Eυ.fiberSum v = 1 := by
  intro v hv
  have h := hbi_hbdry_endgame B hFa v hv
  rw [hlamEq v, hτEq v, hυEq v] at h
  exact h


theorem hxf_hexZ_chi_div (c : ℕ → ℝ)
    {Iυ Ila : Type} (Eυ : HexColumnEmb ℕ Iυ) (Ela : HexColumnEmb ℕ Ila)
    (tau : ℕ → ℝ) (hτnn : ∀ v, 0 ≤ tau v)
    
    (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
    (hτEq : ∀ v, (B v).tau = tau v)
    (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
    (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
    (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
    
    (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
    
    {Iτ : Type} (S : HexSideContour Iτ tau)
    (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  set ups : ℕ → ℝ := Eυ.fiberSum with hupsdef
  set lam : ℕ → ℝ := hbr_lamCum (Ela.fiberSum) with hlamdef
  
  have hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1 := by
    intro v hv
    rw [hlamdef, hupsdef]
    exact hxf_bdry_combined Eυ Ela tau B hFa hlamEq hτEq hυEq v hv
  
  have hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1) := by
    intro v _
    exact hbr_cutB_of_bijection Eυ (Cut v) v (eB v) (hwB v)
  
  have hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v := by
    intro v _
    refine hbr_cutD_of_bijection Ela (Cut v) lam v ?_ (eD v) (hwD v)
    rw [hlamdef]; exact hbr_lamCum_telescope (Ela.fiberSum) v
  
  have hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1) := by
    intro v _
    rw [hlamdef]
    exact hbr_lamCum_mono (Ela.fiberSum) (fun n => hbr_fiberSum_nonneg Ela n) v
  
  have hυnn : ∀ v, 0 ≤ ups v := fun v => hbr_fiberSum_nonneg Eυ v
  
  have hEυc : Eυ.fiberSum = ups := rfl
  
  
  exact hexZ_chi_div_seams_closed c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB S.Eτ hEτ (hzd_tau_side_diverges S) Eυ hEυ hEυc


theorem hxf_hex_connective_constant
    (c : ℕ → ℝ)
    (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    
    {Iυ Ila : Type} (Eυ : HexColumnEmb ℕ Iυ) (Ela : HexColumnEmb ℕ Ila)
    (tau : ℕ → ℝ) (hτnn : ∀ v, 0 ≤ tau v)
    (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
    (hτEq : ∀ v, (B v).tau = tau v)
    (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
    (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
    (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
    (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
    
    {Iτ : Type} (S : HexSideContour Iτ tau)
    (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    
    (Col : ∀ T, HexColumn T hexChiE)
    (HW : ∀ x, 0 < x → x < hexChiE →
      ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  
  have hdiv : ¬ Summable (fun n => c n * hexChiE ^ n) :=
    hxf_hexZ_chi_div c Eυ Ela tau hτnn B hFa hlamEq hτEq hυEq
      Cut eB hwB eD hwD hυpos S hEτ hEυ
  
  have hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n) :=
    hexConnAssembly_conv c (fun n => le_trans zero_le_one (hge n)) Col HW
  
  exact hex_connective_constant c hge hsub hdiv hconv


theorem hxf_hexChiE_lt_one : hexChiE < 1 := by
  unfold hexChiE; rw [div_lt_one hex_sqrt_pos]
  calc (1:ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < Real.sqrt (2 + Real.sqrt 2) := by
        apply Real.sqrt_lt_sqrt (by norm_num); have := Real.sqrt_nonneg 2; linarith


theorem hxf_one_le_chiInv : 1 ≤ hexChiE⁻¹ := by
  rw [le_inv_comm₀ one_pos hexChiE_pos, inv_one]; exact le_of_lt hxf_hexChiE_lt_one


end StatMech.Universality
