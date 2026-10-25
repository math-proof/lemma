/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Def.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose


namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


theorem hbr_lamCum_telescope (f : ℕ → ℝ) (v : ℕ) :
    hbr_lamCum f (v + 1) - hbr_lamCum f v = f (v + 1) := by
  unfold hbr_lamCum
  rw [Finset.sum_range_succ]
  ring


theorem hbr_lamCum_mono (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (v : ℕ) :
    hbr_lamCum f v ≤ hbr_lamCum f (v + 1) := by
  unfold hbr_lamCum
  rw [Finset.sum_range_succ (f := f) (n := v + 1)]
  linarith [hf (v + 1)]


theorem hbr_cutD_of_bijection {W Ila : Type} (Ela : HexColumnEmb W Ila) {K : ℝ}
    (Cut : HexHighestCut K) (lam : ℕ → ℝ) (v : ℕ)
    (htel : lam (v + 1) - lam v = Ela.fiberSum (v + 1))
    (e : Cut.D ≃ {i : Ila // Ela.scale i = v + 1})
    (hw : ∀ d, Cut.wtγ d = Ela.wtSAW (Ela.emb (e d).1)) :
    (∑' d, Cut.wtγ d) = lam (v + 1) - lam v := by
  rw [htel]
  unfold HexColumnEmb.fiberSum
  rw [← Equiv.tsum_eq e (fun i => Ela.wtSAW (Ela.emb i.1))]
  exact tsum_congr hw


theorem hbr_hexZ_chi_div_of_bijections (c : ℕ → ℝ)
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    {Ila : Type} (Ela : HexColumnEmb ℕ Ila)
    (tau : ℕ → ℝ) (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    
    (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
    (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
    (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
    
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * hbr_lamCum (Ela.fiberSum) v + hexCt * tau v + Eυ.fiberSum v = 1)
    
    (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
    
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  set ups : ℕ → ℝ := Eυ.fiberSum with hupsdef
  set lam : ℕ → ℝ := hbr_lamCum (Ela.fiberSum) with hlamdef
  
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
  
  exact hexZ_chi_div_from_geometry_recon c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc


end StatMech.Universality
