/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Def.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part2
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


theorem triangleFKGlobalConfigSum_eq_sweepSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) :
    triangleFKGlobalConfigSum y0 y1 y2 external =
      triangleFKGlobalSweepSum y0 y1 y2 external := by
  classical
  unfold triangleFKGlobalConfigSum triangleFKGlobalSweepSum
  let classify : (ι → LocalConfig) →
      (ι → ThreeTerminalConnectivity) := fun config i =>
    triangleFKLocalConnectivity (config i)
  calc
    (∑ config : ι → LocalConfig,
        external (classify config) *
          ∏ i, triangleFKLocalOddsWeight y0 y1 y2 (config i)) =
      ∑ sector : ι → ThreeTerminalConnectivity,
        ∑ config : ι → LocalConfig,
          if classify config = sector then
            external (classify config) *
              ∏ i, triangleFKLocalOddsWeight y0 y1 y2 (config i)
          else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro config _
            simp
    _ = ∑ sector : ι → ThreeTerminalConnectivity,
        external sector *
          ∏ i, ∑ omega : LocalConfig,
            if triangleFKLocalConnectivity omega = sector i then
              triangleFKLocalOddsWeight y0 y1 y2 omega else 0 := by
      apply Finset.sum_congr rfl
      intro sector _
      rw [← finiteLocalConfig_fiber_sum_eq_prod]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro config _
      by_cases h : classify config = sector <;> simp [h, classify]
    _ = ∑ sector : ι → ThreeTerminalConnectivity,
        external sector *
          ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i) := by
      apply Finset.sum_congr rfl
      intro sector _
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact triangleFKLocalOddsWeight_fiber y0 y1 y2 (sector i)


theorem starFKGlobalConfigSum_eq_sweepSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) :
    starFKGlobalConfigSum q y0 y1 y2 external =
      starFKGlobalSweepSum q y0 y1 y2 external := by
  classical
  unfold starFKGlobalConfigSum starFKGlobalSweepSum
  let classify : (ι → LocalConfig) →
      (ι → ThreeTerminalConnectivity) := fun config i =>
    starFKLocalConnectivity (config i)
  calc
    (∑ config : ι → LocalConfig,
        external (classify config) *
          ∏ i, starFKLocalOddsWeight q y0 y1 y2 (config i)) =
      ∑ sector : ι → ThreeTerminalConnectivity,
        ∑ config : ι → LocalConfig,
          if classify config = sector then
            external (classify config) *
              ∏ i, starFKLocalOddsWeight q y0 y1 y2 (config i)
          else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro config _
            simp
    _ = ∑ sector : ι → ThreeTerminalConnectivity,
        external sector *
          ∏ i, ∑ omega : LocalConfig,
            if starFKLocalConnectivity omega = sector i then
              starFKLocalOddsWeight q y0 y1 y2 omega else 0 := by
      apply Finset.sum_congr rfl
      intro sector _
      rw [← finiteLocalConfig_fiber_sum_eq_prod]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro config _
      by_cases h : classify config = sector <;> simp [h, classify]
    _ = ∑ sector : ι → ThreeTerminalConnectivity,
        external sector *
          ∏ i, starFKTerminalWeight q y0 y1 y2 (sector i) := by
      apply Finset.sum_congr rfl
      intro sector _
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact starFKLocalOddsWeight_fiber q y0 y1 y2 (sector i)


end StatMech.FK.PeriodicPlanar
