/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part5
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem cubicalInternalCentralWilsonExpectation_le_fixed_succ
    {K : Real} (hK : 0 <= K) (n m : Nat)
    (hnm : centralSquareSide n <= m) :
    cubicalInternalCentralWilsonExpectation K n m hnm <=
      cubicalFixedLoopWilsonSequence K (centralSquareSide n)
        (centralSquareSide n) (m + 1) := by
  have hinnerXY : m + centralSquareSide n <= oddCubeSide m := by
    dsimp [oddCubeSide]
    omega
  have hinnerZ : m + 0 <= oddCubeSide m := by
    dsimp [oddCubeSide]
    omega
  have houterXY : 1 + oddCubeSide m <=
      (m + 1) + centralSquareSide n + (m + 1) := by
    dsimp [oddCubeSide, centralSquareSide]
    omega
  have houterZ : 1 + oddCubeSide m <= (m + 1) + (m + 1) := by
    dsimp [oddCubeSide]
    omega
  let L := cubicalXYLoop
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (0 : Fin 1)
  let inner := cubicalEdgeChart m m m
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (A := oddCubeSide m) (B := oddCubeSide m) (C := oddCubeSide m)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega)
  let outer := cubicalEdgeChart 1 1 1
    (a := oddCubeSide m) (b := oddCubeSide m) (c := oddCubeSide m)
    (A := (m + 1) + centralSquareSide n + (m + 1))
    (B := (m + 1) + centralSquareSide n + (m + 1))
    (C := (m + 1) + (m + 1))
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega)
  let target := cubicalEdgeChart (m + 1) (m + 1) (m + 1)
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (A := (m + 1) + centralSquareSide n + (m + 1))
    (B := (m + 1) + centralSquareSide n + (m + 1))
    (C := (m + 1) + (m + 1))
    (by omega) (by omega) (by omega)
  have hmap : (L.map inner).map outer = L.map target := by
    rw [Finset.map_map]
    congr 1
    ext e
    simpa [inner, outer, target, Nat.add_comm] using
      (cubicalEdgeChart_comp_apply m m m 1 1 1
        hinnerXY hinnerXY hinnerZ houterXY houterXY houterZ e)
  have h := cubicalWilsonExpectation_le_chart
    (a := oddCubeSide m) (b := oddCubeSide m) (c := oddCubeSide m)
    (A := (m + 1) + centralSquareSide n + (m + 1))
    (B := (m + 1) + centralSquareSide n + (m + 1))
    (C := (m + 1) + (m + 1))
    1 1 1
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega) hK (L.map inner)
  rw [hmap] at h
  simpa [cubicalInternalCentralWilsonExpectation,
    gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed,
    cubicalFixedLoopWilsonSequence, cubicalPaddedWilsonExpectation,
    L, inner, target] using h


theorem cubicalFixedLoopWilsonSequence_le_internal
    {K : Real} (hK : 0 <= K) (n t m : Nat)
    (hnm : centralSquareSide n <= m)
    (htm : t + centralSquareSide n <= m + 1) :
    cubicalFixedLoopWilsonSequence K (centralSquareSide n)
        (centralSquareSide n) t <=
      cubicalInternalCentralWilsonExpectation K n m hnm := by
  have htm' : t <= m := by
    have hpos : 1 <= centralSquareSide n := by simp [centralSquareSide]
    omega
  have houterXY : m - t + (t + centralSquareSide n + t) <=
      oddCubeSide m := by
    dsimp [oddCubeSide]
    omega
  have houterZ : m - t + (t + t) <= oddCubeSide m := by
    dsimp [oddCubeSide]
    omega
  let L := cubicalXYLoop
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (0 : Fin 1)
  let inner := cubicalEdgeChart t t t
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (A := t + centralSquareSide n + t)
    (B := t + centralSquareSide n + t) (C := t + t)
    (by omega) (by omega) (by omega)
  let outer := cubicalEdgeChart (m - t) (m - t) (m - t)
    (a := t + centralSquareSide n + t)
    (b := t + centralSquareSide n + t) (c := t + t)
    (A := oddCubeSide m) (B := oddCubeSide m) (C := oddCubeSide m)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega)
  let target := cubicalEdgeChart m m m
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (A := oddCubeSide m) (B := oddCubeSide m) (C := oddCubeSide m)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega)
  have hmap : (L.map inner).map outer = L.map target := by
    rw [Finset.map_map]
    congr 1
    ext e
    simpa [inner, outer, target, Nat.sub_add_cancel htm'] using
      (cubicalEdgeChart_comp_apply t t t (m - t) (m - t) (m - t)
        (by omega) (by omega) (by omega)
        houterXY houterXY houterZ e)
  have h := cubicalWilsonExpectation_le_chart
    (a := t + centralSquareSide n + t)
    (b := t + centralSquareSide n + t) (c := t + t)
    (A := oddCubeSide m) (B := oddCubeSide m) (C := oddCubeSide m)
    (m - t) (m - t) (m - t)
    houterXY houterXY houterZ hK (L.map inner)
  rw [hmap] at h
  simpa [cubicalInternalCentralWilsonExpectation,
    gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed,
    cubicalFixedLoopWilsonSequence, cubicalPaddedWilsonExpectation,
    L, inner, target] using h


theorem cubicalInternalCentralWilsonExpectation_tendsto
    {K : Real} (hK : 0 < K) (n : Nat)
    (m : Nat -> Nat) (hm : ∀ k, centralSquareSide n <= m k)
    (hmTop : Tendsto m atTop atTop) :
    Tendsto (fun k => cubicalInternalCentralWilsonExpectation K n (m k) (hm k))
      atTop
      (nhds (cubicalInfiniteVolumeWilsonExpectation K
        (centralSquareSide n) (centralSquareSide n))) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    have hcanon : ∀ᶠ t : Nat in atTop,
        x < cubicalFixedLoopWilsonSequence K (centralSquareSide n)
          (centralSquareSide n) t :=
      (cubicalFixedLoopWilsonSequence_tendsto hK
        (centralSquareSide n) (centralSquareSide n)).eventually
        (Ioi_mem_nhds hx)
    obtain ⟨t, ht⟩ := eventually_atTop.1 hcanon
    filter_upwards [hmTop.eventually
      (eventually_ge_atTop (t + centralSquareSide n))] with k hk
    exact (ht t le_rfl).trans_le
      (cubicalFixedLoopWilsonSequence_le_internal hK.le n t (m k)
        (hm k) (by omega))
  · intro y hy
    exact Eventually.of_forall fun k =>
      (cubicalInternalCentralWilsonExpectation_le_fixed_succ
        hK.le n (m k) (hm k)).trans_lt
      ((cubicalPaddedWilsonExpectation_le_infiniteVolume hK
        (centralSquareSide n) (centralSquareSide n)
        (m k + 1) (m k + 1) (m k + 1) (m k + 1)
        (m k + 1) (m k + 1)).trans_lt hy)


theorem centralCylinderPlusCorrProduct_le_infiniteWilson
    (K : Real) (hK : 0 < K) (n : Nat) :
    (∏ uv ∈ centralCylinderPairs n,
      (1 - plusCorr 3 (gaugeDualCoupling K)
        (centralCylinderVertexSite n uv.1)
        (centralCylinderVertexSite n uv.2))) <=
      cubicalInfiniteVolumeWilsonExpectation K
        (centralSquareSide n) (centralSquareSide n) := by
  obtain ⟨m, hm, hmTop, hprod⟩ :=
    exists_internalCentralCylinderProduct_tendsto
      (gaugeDualCoupling K) n
  have hwilson := cubicalInternalCentralWilsonExpectation_tendsto
    hK n m (fun k => (hm k).le) hmTop
  exact le_of_tendsto_of_tendsto hprod hwilson
    (Eventually.of_forall fun k => by
      simpa [internalCentralPairCorrelation,
        cubicalInternalCentralWilsonExpectation] using
        (cubicalInternalCentralWilsonExpectation_ge_fixed_product
          n (m k) (hm k) K hK))


theorem l1dist_centralCylinderVertexSite
    (n : Nat) (uv :
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n) ×
        CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n))
    (huv : uv ∈ centralCylinderPairs n) :
    l1dist 3 (centralCylinderVertexSite n uv.1)
        (centralCylinderVertexSite n uv.2) =
      cubicalDualL1 uv.1 uv.2 := by
  have hmem := Finset.mem_product.mp huv
  rcases uv with ⟨u, v⟩
  cases u with
  | none => exact (none_not_mem_centralLowerBoundaryVertices n hmem.1).elim
  | some q =>
      cases v with
      | none => exact (none_not_mem_centralUpperLayerVertices n hmem.2).elim
      | some r =>
          let m := centralSquareSide n + 1
          have hnm : centralSquareSide n < m := by dsimp [m]; omega
          rw [centralCylinderVertexSite, centralCylinderVertexSite,
            ← oddCubicalCenteredSite_internalCentralCellEmbedding n m hnm q,
            ← oddCubicalCenteredSite_internalCentralCellEmbedding n m hnm r,
            l1dist_oddCubicalCenteredSite]
          simpa only [internalCentralVertexEmbedding_some] using
            (cubicalDualL1_internalCentralVertexEmbedding
              n m hnm (some q) (some r))


theorem centralCylinderPairs_l1_ge_one
    (n : Nat) (uv :
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n) ×
        CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n))
    (huv : uv ∈ centralCylinderPairs n) :
    (1 : Real) <= cubicalDualL1 uv.1 uv.2 := by
  have hmem := Finset.mem_product.mp huv
  rcases uv with ⟨u, v⟩
  cases u with
  | none => exact (none_not_mem_centralLowerBoundaryVertices n hmem.1).elim
  | some q =>
      cases v with
      | none => exact (none_not_mem_centralUpperLayerVertices n hmem.2).elim
      | some r =>
          have hq := (mem_centralLowerBoundaryVertices_iff n q).mp hmem.1
          obtain ⟨ij, _, hr⟩ := Finset.mem_image.mp hmem.2
          simp only [Option.some.injEq] at hr
          subst r
          simp only [cubicalDualL1]
          exact_mod_cast (show 1 <=
            Nat.dist q.x.val ij.1.val + Nat.dist q.y.val ij.2.val +
              Nat.dist q.z.val (centralSquareSide n) by
            rw [Nat.dist_eq_sub_of_le hq.1.le]
            omega)


theorem centralCylinderPairs_exp_l1_sum_le
    (decay : Real) (hdecay : 0 < decay) (n : Nat) :
    (∑ uv ∈ centralCylinderPairs n,
      Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) <=
      20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 * centralSquareSide n := by
  rw [show (∑ uv ∈ centralCylinderPairs n,
      Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) =
      ∑ uv ∈ centralCylinderPairs n,
        Real.exp (-decay) ^ cubicalDualL1 uv.1 uv.2 by
    apply Finset.sum_congr rfl
    intro uv _
    exact exp_neg_mul_natCast_eq_pow_exp_neg decay _]
  calc
    _ <= squareLowerCapExpSum (Real.exp (-decay)) (centralSquareSide n) +
        squareXSideExpSum (Real.exp (-decay))
          (0 : Fin (centralSquareSide n)) +
        squareXSideExpSum (Real.exp (-decay)) (Fin.last n) +
        squareYSideExpSum (Real.exp (-decay))
          (0 : Fin (centralSquareSide n)) +
        squareYSideExpSum (Real.exp (-decay)) (Fin.last n) :=
      centralLowerBoundary_doubleSum_le_coordinate (Real.exp_pos _).le n
    _ <= 20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 * centralSquareSide n :=
      squareCylinderCoordinateExpSum_le_inv (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith)
        (0 : Fin (centralSquareSide n)) (Fin.last n)
        (0 : Fin (centralSquareSide n)) (Fin.last n)


theorem exists_cubicalInfiniteVolumeWilson_perimeterLower_of_dual_lt_betaC
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < betaC 3) :
    ∃ decay > 0, ∀ n,
      Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) *
            (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
          centralSquareSide n) <=
        cubicalInfiniteVolumeWilsonExpectation K
          (centralSquareSide n) (centralSquareSide n) := by
  have hdual0 : 0 <= gaugeDualCoupling K :=
    (gaugeDualCoupling_pos hK).le
  obtain ⟨decay, hdecay, hcorr⟩ :=
    plusCorr_allPairs_exponential_of_lt_betaC (d := 3) (by norm_num)
      hdual0 hlt
  refine ⟨decay, hdecay, fun n => ?_⟩
  let corr := fun uv :
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n) ×
        CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n) =>
    plusCorr 3 (gaugeDualCoupling K)
      (centralCylinderVertexSite n uv.1)
      (centralCylinderVertexSite n uv.2)
  apply gauge_perimeterLaw_of_product_and_sum_bounds
    (Real.exp_pos _) (by rw [Real.exp_lt_one_iff]; linarith)
    (centralCylinderPairs n) corr
  · intro uv _
    exact plusCorr_nonneg (gaugeDualCoupling K) hdual0 _ _
  · intro uv huv
    calc
      corr uv <= Real.exp
          (-decay * (l1dist 3
            (centralCylinderVertexSite n uv.1)
            (centralCylinderVertexSite n uv.2) : Real)) := hcorr _ _
      _ = Real.exp
          (-decay * (cubicalDualL1 uv.1 uv.2 : Real)) := by
        rw [l1dist_centralCylinderVertexSite n uv huv]
      _ <= Real.exp (-decay) := by
        rw [Real.exp_le_exp]
        nlinarith [centralCylinderPairs_l1_ge_one n uv huv]
  · exact centralCylinderPlusCorrProduct_le_infiniteWilson K hK n
  · calc
      (∑ uv ∈ centralCylinderPairs n, corr uv) <=
          ∑ uv ∈ centralCylinderPairs n,
            Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real)) := by
        apply Finset.sum_le_sum
        intro uv huv
        rw [← l1dist_centralCylinderVertexSite n uv huv]
        exact hcorr _ _
      _ <= 20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 *
          centralSquareSide n :=
        centralCylinderPairs_exp_l1_sum_le decay hdecay n


theorem isingBetaC_three_pos : 0 < betaC 3 := by
  have hbdd := tildeBetaCIsingSet_bddAbove (d := 3) (by norm_num)
  have hcrit := tildeBetaCIsing_pos (d := 3) (by norm_num)
  have hsqrt : ∀ beta, tildeBetaCIsing 3 <= beta ->
      Real.sqrt (1 - (tildeBetaCIsing 3 / beta) ^ 2) <=
        magnetization 3 beta := fun beta hbeta =>
    sct_magnetization_meanfield_lower_bound_integrated 3 hbdd hcrit hbeta
  rw [bc_eq_ising_of_sqrt_and_susceptibility (d := 3) (by norm_num) hsqrt]
  exact hcrit


theorem exists_cubicalInfiniteVolumeWilson_perimeterLower_of_critical_lt
    (K : Real) (hK : 0 < K)
    (hhigh : gaugeCriticalCoupling (betaC 3) < K) :
    ∃ decay > 0, ∀ n,
      Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) *
            (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
          centralSquareSide n) <=
        cubicalInfiniteVolumeWilsonExpectation K
          (centralSquareSide n) (centralSquareSide n) := by
  apply exists_cubicalInfiniteVolumeWilson_perimeterLower_of_dual_lt_betaC
    K hK
  exact (gaugeDualCoupling_lt_iff_gaugeCriticalCoupling_lt
    hK isingBetaC_three_pos).2 hhigh

end
end StatMech.FrontierA
