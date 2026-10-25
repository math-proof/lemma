/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part15
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part2
open Finset Set
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteTriangle_sectorBoundaryObservable_eq_indicator
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    triHexFKTerminalBoundaryReachObservable
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0)
        (fun z => triangleFKLocalConnectivity
          (triHexPlanarFiniteTriangleConfigEquiv n omega z)) =
      triHexPlanarFiniteTriangleBoundaryReachIndicator n omega := by
  classical
  unfold triHexFKTerminalBoundaryReachObservable
    triHexPlanarFiniteTriangleBoundaryReachIndicator
  congr 1
  apply propext
  constructor <;> rintro ⟨y, hy, hreach⟩
  · exact ⟨y, hy,
      (triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
        n omega _ _).mpr hreach⟩
  · exact ⟨y, hy,
      (triHexPlanarFiniteTriangle_openSub_reachable_iff_sector
        n omega _ _).mp hreach⟩


theorem triHexPlanarFiniteTriangle_wiredActiveNumer_boundary_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y) :
    wiredActiveNumer (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q
        (triHexPlanarFiniteTriangleBoundaryReachIndicator n) =
      (∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) *
        triangleFKGlobalConfigSum y y y
          (fun sector => triHexFKTerminalWiredExternal q
              (triHexPlanarFiniteTerminalMap n)
              (triHexPlanarFiniteBoundary n) sector *
            triHexFKTerminalBoundaryReachObservable
              (triHexPlanarFiniteTerminalMap n)
              (triHexPlanarFiniteBoundary n)
              (triHexPlanarFiniteTerminalMap n
                (triHexPlanarFiniteRootCell n) 0) sector) := by
  classical
  unfold wiredActiveNumer triangleFKGlobalConfigSum
  rw [← (triHexPlanarFiniteTriangleConfigEquiv n).symm.sum_comp
    (fun omega => triHexPlanarFiniteTriangleBoundaryReachIndicator n omega *
      wiredActiveWeight (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triHexPlanarFiniteTriangle_wiredActiveWeight_eq n hodds]
  rw [← triHexPlanarFiniteTriangle_sectorBoundaryObservable_eq_indicator
    n ((triHexPlanarFiniteTriangleConfigEquiv n).symm config)]
  rw [(triHexPlanarFiniteTriangleConfigEquiv n).apply_symm_apply config]
  ring


theorem triHexPlanarFiniteTriangle_wiredActiveRatio_eq
    (n : Nat) {p y q : Real} (hp1 : p ≠ 1)
    (hodds : p = (1 - p) * y) :
    wiredActiveRatio (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q
        (triHexPlanarFiniteTriangleBoundaryReachIndicator n) =
      triangleFKFiniteWiredBoundaryReachRatio q y y y
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) := by
  unfold wiredActiveRatio triangleFKFiniteWiredBoundaryReachRatio
  rw [triHexPlanarFiniteTriangle_wiredActiveNumer_boundary_eq n hodds,
    triHexPlanarFiniteTriangle_wiredActiveZ_eq n hodds]
  apply mul_div_mul_left
  rw [Finset.prod_ne_zero_iff]
  intro _ _
  exact sub_ne_zero.mpr (Ne.symm hp1)


theorem triHexPlanarFiniteStar_isolatedCenterFactor_product
    (n : Nat) (q : Real)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    (∏ z, starFKIsolatedCenterFactor q
      (triHexPlanarFiniteStarConfigEquiv n omega z)) =
      q ^ Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) := by
  unfold starFKIsolatedCenterFactor TriHexPlanarFiniteStarIsolatedCenter
  have h := @fintype_prod_ite_eq_pow_card_subtype
    (TriHexPlanarFiniteCell n) inferInstance
      (fun z => triHexPlanarFiniteStarConfigEquiv n omega z =
        (false, false, false)) inferInstance inferInstance q
  rw [h]


theorem triHexPlanarFiniteStar_localOddsProduct
    (n : Nat) (q y : Real)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    (∏ z, starFKLocalOddsWeight q y y y
      (triHexPlanarFiniteStarConfigEquiv n omega z)) =
      q ^ Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) *
        ∏ e : (triHexPlanarFiniteStarGraph n).edgeSet,
          if omega e then y else 1 := by
  rw [starFKGlobalLocalOdds_eq_isolated_mul_directionProduct,
    triHexPlanarFiniteStar_isolatedCenterFactor_product]
  congr 1
  calc
    (∏ a : TriHexPlanarFiniteCell n × Fin 3,
        if triHexLocalDirection
            (triHexPlanarFiniteStarConfigEquiv n omega a.1) a.2 then
          triHexDirectionOdds y y y a.2 else 1) =
      ∏ a : TriHexPlanarFiniteCell n × Fin 3,
        if omega (triHexPlanarFiniteStarEdgeEquiv n a) then y else 1 := by
          apply Fintype.prod_congr
          rintro ⟨z, i⟩
          fin_cases i <;> rfl
    _ = ∏ e : (triHexPlanarFiniteStarGraph n).edgeSet,
        if omega e then y else 1 := by
      simpa using (triHexPlanarFiniteStarEdgeEquiv n).prod_comp
        (fun e => if omega e then y else 1)


theorem triHexPlanarFiniteStar_edgeProduct
    (n : Nat) {p y : Real} (hodds : p = (1 - p) * y)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    edgeProduct (triHexPlanarFiniteStarGraph n) p
        (extendActive (triHexPlanarFiniteStarGraph n) omega) =
      (∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) *
        ∏ e : (triHexPlanarFiniteStarGraph n).edgeSet,
          if omega e then y else 1 := by
  change edgeProductW (triHexPlanarFiniteStarGraph n) (fun _ => p)
      (extendActive (triHexPlanarFiniteStarGraph n) omega) = _
  exact edgeProductW_extendActive_odds_factor
    (triHexPlanarFiniteStarGraph n) (fun _ => p) (fun _ => y)
      (fun _ => hodds) omega


theorem triHexPlanarFiniteStar_wiredActiveWeight_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    wiredActiveWeight (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q omega =
      (∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) *
        (triHexFKTerminalWiredExternal q
            (triHexPlanarFiniteTerminalMap n)
            (triHexPlanarFiniteBoundary n)
            (fun z => starFKLocalConnectivity
              (triHexPlanarFiniteStarConfigEquiv n omega z)) *
          ∏ z, starFKLocalOddsWeight q y y y
            (triHexPlanarFiniteStarConfigEquiv n omega z)) := by
  unfold wiredActiveWeight wiredFkWeight
  rw [triHexPlanarFiniteStar_edgeProduct n hodds,
    triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated,
    pow_add, triHexPlanarFiniteStar_localOddsProduct]
  unfold triHexFKTerminalWiredExternal
    triHexPlanarFiniteStarWiredSectorGraph
  ring


theorem triHexPlanarFiniteStar_wiredActiveZ_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y) :
    wiredActiveZ (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q =
      (∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) *
        starFKGlobalConfigSum q y y y
          (triHexFKTerminalWiredExternal q
            (triHexPlanarFiniteTerminalMap n)
            (triHexPlanarFiniteBoundary n)) := by
  classical
  unfold wiredActiveZ starFKGlobalConfigSum
  rw [← (triHexPlanarFiniteStarConfigEquiv n).symm.sum_comp
    (fun omega => wiredActiveWeight (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n) p q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triHexPlanarFiniteStar_wiredActiveWeight_eq n hodds]
  rw [(triHexPlanarFiniteStarConfigEquiv n).apply_symm_apply config]


end
end StatMech.FK.PeriodicPlanar
