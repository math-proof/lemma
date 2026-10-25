/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Def.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


theorem triangleFKLocalOddsWeight_fiber
    (y0 y1 y2 : Real) (connectivity : ThreeTerminalConnectivity) :
    (∑ omega : LocalConfig,
      if triangleFKLocalConnectivity omega = connectivity then
        triangleFKLocalOddsWeight y0 y1 y2 omega else 0) =
      triangleFKTerminalWeight y0 y1 y2 connectivity := by
  fin_cases connectivity <;>
    simp [triangleFKLocalConnectivity, triangleFKLocalOddsWeight,
      triangleFKTerminalWeight, Fintype.sum_prod_type] <;> ring


theorem starFKLocalOddsWeight_fiber
    (q y0 y1 y2 : Real) (connectivity : ThreeTerminalConnectivity) :
    (∑ omega : LocalConfig,
      if starFKLocalConnectivity omega = connectivity then
        starFKLocalOddsWeight q y0 y1 y2 omega else 0) =
      starFKTerminalWeight q y0 y1 y2 connectivity := by
  fin_cases connectivity <;>
    simp [starFKLocalConnectivity, starFKLocalOddsWeight,
      starFKTerminalWeight, Fintype.sum_prod_type] <;> ring


theorem finiteLocalConfig_fiber_sum_eq_prod
    {ι Ω C : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype C] [DecidableEq C]
    (classify : Ω → C) (weight : Ω → Real) (sector : ι → C) :
    (∑ config : ι → Ω,
      if (fun i => classify (config i)) = sector then
        ∏ i, weight (config i) else 0) =
      ∏ i, ∑ omega : Ω,
        if classify omega = sector i then weight omega else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro config _
  by_cases hsector : (fun i => classify (config i)) = sector
  · subst sector
    simp
  · simp only [hsector, if_false]
    obtain ⟨i, hi⟩ : ∃ i, classify (config i) ≠ sector i := by
      by_contra h
      push_neg at h
      exact hsector (funext h)
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]


end StatMech.FK.PeriodicPlanar
