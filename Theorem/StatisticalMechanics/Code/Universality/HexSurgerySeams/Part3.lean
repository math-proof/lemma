/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean -/

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
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part2


namespace StatMech.Universality

open Complex HexWalk List Filter

open scoped Topology BigOperators


theorem hexZ_chi_div_seams_closed (c lam tau ups : ℕ → ℝ)
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
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hexZ_chi_div_from_geometry_recon c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc


theorem hexSeams_powerset_range_tendsto :
    Tendsto (fun N => (Finset.range N).powerset) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro s
  refine ⟨(s.sup (fun t => t.sup id)) + 1, fun M hM => ?_⟩
  intro t ht
  rw [Finset.mem_powerset]
  intro i hi
  rw [Finset.mem_range]
  have h1 : i ≤ t.sup id := Finset.le_sup (f := id) hi
  have h2 : t.sup id ≤ s.sup (fun t => t.sup id) := Finset.le_sup ht
  omega


theorem hexSeams_prod_one_add_mono (f : ℕ → ℝ) (hnn : ∀ i, 0 ≤ f i) :
    Monotone (fun N => ∏ i ∈ Finset.range N, (1 + f i)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Finset.prod_range_succ]
  have hp : (0 : ℝ) ≤ ∏ i ∈ Finset.range n, (1 + f i) :=
    Finset.prod_nonneg (fun i _ => by have := hnn i; linarith)
  nlinarith [hnn n]


theorem hexSeams_prod_one_add_le_tprod (f : ℕ → ℝ) (hnn : ∀ i, 0 ≤ f i)
    (hm : Multipliable (fun i => 1 + f i)) (N : ℕ) :
    ∏ i ∈ Finset.range N, (1 + f i) ≤ ∏' i, (1 + f i) :=
  Monotone.ge_of_tendsto (hexSeams_prod_one_add_mono f hnn)
    (Multipliable.tendsto_prod_tprod_nat hm) N


theorem hexSeams_summable_finset_prod (f : ℕ → ℝ) (hnn : ∀ i, 0 ≤ f i)
    (hm : Multipliable (fun i => 1 + f i)) :
    Summable (fun t : Finset ℕ => ∏ i ∈ t, f i) := by
  apply summable_of_sum_le (c := ∏' i, (1 + f i))
  · intro t; exact Finset.prod_nonneg (fun i _ => hnn i)
  · intro s
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp hexSeams_powerset_range_tendsto) s
    have hsub : s ≤ (Finset.range N).powerset := hN N le_rfl
    calc ∑ t ∈ s, ∏ i ∈ t, f i
        ≤ ∑ t ∈ (Finset.range N).powerset, ∏ i ∈ t, f i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun t _ _ => Finset.prod_nonneg (fun i _ => hnn i))
      _ = ∏ i ∈ Finset.range N, (1 + f i) := (Finset.prod_one_add _).symm
      _ ≤ ∏' i, (1 + f i) := hexSeams_prod_one_add_le_tprod f hnn hm N


theorem tsum_finset_prod_eq_tprod (f : ℕ → ℝ) (hnn : ∀ i, 0 ≤ f i)
    (hm : Multipliable (fun i => 1 + f i)) :
    (∑' t : Finset ℕ, ∏ i ∈ t, f i) = ∏' i, (1 + f i) := by
  have hsum := hexSeams_summable_finset_prod f hnn hm
  have hHS := hsum.hasSum
  have ht1 : Tendsto (fun N => ∑ t ∈ (Finset.range N).powerset, ∏ i ∈ t, f i) atTop
      (𝓝 (∑' t : Finset ℕ, ∏ i ∈ t, f i)) := by
    have := hHS.comp hexSeams_powerset_range_tendsto
    convert this using 1
  have heq : (fun N => ∑ t ∈ (Finset.range N).powerset, ∏ i ∈ t, f i)
      = (fun N => ∏ i ∈ Finset.range N, (1 + f i)) := by
    funext N; exact (Finset.prod_one_add _).symm
  rw [heq] at ht1
  exact tendsto_nhds_unique ht1 (Multipliable.tendsto_prod_tprod_nat hm)


end StatMech.Universality
