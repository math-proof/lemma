/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Structure.StatisticalMechanics.Code.Universality.HexBridge.Part5


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


attribute [instance] HexHWData.Dn_fintype

namespace HexHWData

variable {c υ : ℕ → ℝ} {x : ℝ} {N : ℕ}


theorem partial_bound (H : HexHWData c υ x N) :
    ∑ n ∈ Finset.range N, c n * x ^ n ≤ 2 * (∏' T, (1 + υ T)) ^ 2 := by
  classical
  
  have hprodSumm : Summable (fun p : H.S × H.S => H.wtS p.1 * H.wtS p.2) :=
    H.S_summable.mul_of_nonneg H.S_summable H.wtS_nn H.wtS_nn
  have hprodEq : (∑' p : H.S × H.S, H.wtS p.1 * H.wtS p.2) = (∑' s, H.wtS s) ^ 2 := by
    rw [sq, ← H.S_summable.tsum_mul_tsum H.S_summable hprodSumm]
  
  have hcap : (∑ d, H.wtγ d) ≤ (∑' s, H.wtS s) ^ 2 := by
    calc (∑ d, H.wtγ d)
        ≤ ∑ d : H.Dn, H.wtS (H.decomp d).1 * H.wtS (H.decomp d).2 :=
          Finset.sum_le_sum (fun d _ => H.weight_bound d)
      _ = ∑ p ∈ Finset.univ.image H.decomp, H.wtS p.1 * H.wtS p.2 := by
          rw [Finset.sum_image (fun a _ b _ h => H.decomp_inj h)]
      _ ≤ ∑' p : H.S × H.S, H.wtS p.1 * H.wtS p.2 :=
          Summable.sum_le_tsum _ (fun p _ => mul_nonneg (H.wtS_nn _) (H.wtS_nn _)) hprodSumm
      _ = (∑' s, H.wtS s) ^ 2 := hprodEq
  
  rw [← H.partial_eq]
  calc (∑ d, H.wtγ d) ≤ (∑' s, H.wtS s) ^ 2 := hcap
    _ = (∏' T, (1 + υ T)) ^ 2 := by rw [H.half_sum_eq]
    _ ≤ 2 * (∏' T, (1 + υ T)) ^ 2 := by nlinarith [sq_nonneg (∏' T, (1 + υ T))]

end HexHWData


theorem hexZ_conv_from_geometry (c : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hlt : x < hexChiE)
    (hc : ∀ n, 0 ≤ c n)
    (C : ∀ T, HexColumn T hexChiE)
    (H : ∀ N, HexHWData c (fun T => (C T).colSum x) x N) :
    Summable (fun n => c n * x ^ n) := by
  set upsx : ℕ → ℝ := fun T => (C T).colSum x with hupsx
  refine hexZ_conv c upsx x hx hlt hc ?_ ?_ ?_
  · 
    intro T; exact (C T).colSum_nonneg hx
  · 
    intro T; exact (C T).colSum_le_pow hx hexChiE_pos (le_of_lt hlt)
  · 
    intro N; exact (H N).partial_bound


theorem hexRec_term_of_cut (lam ups : ℕ → ℝ) (v : ℕ)
    (Cut : HexHighestCut hexChiE)
    (hD : (∑' d, Cut.wtγ d) = lam (v + 1) - lam v)
    (hB : (∑' b, Cut.wtB b) = ups (v + 1)) :
    lam (v + 1) - lam v ≤ hexChiE * (ups (v + 1)) ^ 2 := by
  have hrb := Cut.recursion_bound (le_of_lt hexChiE_pos)
  rw [hD, hB] at hrb
  exact hrb


theorem hexZ_chi_div_from_geometry (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  have hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE * (ups (v + 1)) ^ 2 :=
    fun v hv => hexRec_term_of_cut lam ups v (Cut v) (hCutD v hv) (hCutB v hv)
  
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
  exact hexZ_chi_div c lam tau ups hbdry hrec hlamMono hυpos hυnn hτnn hτcol hυemb

end StatMech.Universality
