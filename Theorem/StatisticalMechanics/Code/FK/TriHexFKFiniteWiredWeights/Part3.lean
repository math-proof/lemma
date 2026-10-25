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
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part3
open Finset Set
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteStar_sectorBoundaryObservable_eq_indicator
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet) :
    triHexFKTerminalBoundaryReachObservable
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0)
        (fun z => starFKLocalConnectivity
          (triHexPlanarFiniteStarConfigEquiv n omega z)) =
      triHexPlanarFiniteStarBoundaryReachIndicator n omega := by
  classical
  unfold triHexFKTerminalBoundaryReachObservable
    triHexPlanarFiniteStarBoundaryReachIndicator
  congr 1
  apply propext
  constructor <;> rintro ⟨y, hy, hreach⟩
  · exact ⟨y, hy,
      (triHexPlanarFiniteStar_openSub_white_reachable_iff_sector
        n omega _ _).mpr hreach⟩
  · exact ⟨y, hy,
      (triHexPlanarFiniteStar_openSub_white_reachable_iff_sector
        n omega _ _).mp hreach⟩


theorem triHexPlanarFiniteStar_wiredActiveNumer_boundary_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y) :
    wiredActiveNumer (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q
        (triHexPlanarFiniteStarBoundaryReachIndicator n) =
      (∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) *
        starFKGlobalConfigSum q y y y
          (fun sector => triHexFKTerminalWiredExternal q
              (triHexPlanarFiniteTerminalMap n)
              (triHexPlanarFiniteBoundary n) sector *
            triHexFKTerminalBoundaryReachObservable
              (triHexPlanarFiniteTerminalMap n)
              (triHexPlanarFiniteBoundary n)
              (triHexPlanarFiniteTerminalMap n
                (triHexPlanarFiniteRootCell n) 0) sector) := by
  classical
  unfold wiredActiveNumer starFKGlobalConfigSum
  rw [← (triHexPlanarFiniteStarConfigEquiv n).symm.sum_comp
    (fun omega => triHexPlanarFiniteStarBoundaryReachIndicator n omega *
      wiredActiveWeight (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triHexPlanarFiniteStar_wiredActiveWeight_eq n hodds]
  rw [← triHexPlanarFiniteStar_sectorBoundaryObservable_eq_indicator
    n ((triHexPlanarFiniteStarConfigEquiv n).symm config)]
  rw [(triHexPlanarFiniteStarConfigEquiv n).apply_symm_apply config]
  ring


theorem triHexPlanarFiniteStar_wiredActiveRatio_eq
    (n : Nat) {p y q : Real} (hp1 : p ≠ 1)
    (hodds : p = (1 - p) * y) :
    wiredActiveRatio (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q
        (triHexPlanarFiniteStarBoundaryReachIndicator n) =
      starFKFiniteWiredBoundaryReachRatio q y y y
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) := by
  unfold wiredActiveRatio starFKFiniteWiredBoundaryReachRatio
  rw [triHexPlanarFiniteStar_wiredActiveNumer_boundary_eq n hodds,
    triHexPlanarFiniteStar_wiredActiveZ_eq n hodds]
  apply mul_div_mul_left
  rw [Finset.prod_ne_zero_iff]
  intro _ _
  exact sub_ne_zero.mpr (Ne.symm hp1)


end
end StatMech.FK.PeriodicPlanar
