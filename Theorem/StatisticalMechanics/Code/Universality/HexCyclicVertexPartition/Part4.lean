/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Structure.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem HexCyclicLaunch.succ_newMid
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts) :
    hexCyclicNewMid a h0 ts (-1) =
      labelMid v du (hexCyclicSucc j) := by
  have hend : hexInfra_midAccum a h0 ts = labelMid v du j := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact L.endsAt
  rw [hexCyclicNewMid, hend,
    show hexInfra_headAccum h0 ts + (-1) =
      hexInfra_headAccum h0 ts - 1 by ring]
  have hstep : halfStep (hexInfra_headAccum h0 ts - 1) =
      -(hexOmega * halfStep (hexInfra_headAccum h0 ts)) := by
    unfold halfStep
    have key := hexUnit_add_three (hexInfra_headAccum h0 ts - 1)
    rw [show (hexInfra_headAccum h0 ts - 1 + 3 : ℤ) =
      hexInfra_headAccum h0 ts + 2 by ring, hexUnit_add_two] at key
    linear_combination (1 / 2 : ℂ) * key
  rw [hstep, hexCyclicSucc_mid]
  linear_combination (1 - hexOmega) * L.lastVertex


theorem HexCyclicLaunch.pred_newMid
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts) :
    hexCyclicNewMid a h0 ts 1 =
      labelMid v du (hexCyclicPred j) := by
  have hend : hexInfra_midAccum a h0 ts = labelMid v du j := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact L.endsAt
  rw [hexCyclicNewMid, hend]
  have hstep : halfStep (hexInfra_headAccum h0 ts + 1) =
      -(hexOmega ^ 2 * halfStep (hexInfra_headAccum h0 ts)) := by
    unfold halfStep
    have key := hexUnit_add_three (hexInfra_headAccum h0 ts + 1)
    rw [show (hexInfra_headAccum h0 ts + 1 + 3 : ℤ) =
      hexInfra_headAccum h0 ts + 4 by ring, hexUnit_add_four] at key
    linear_combination (1 / 2 : ℂ) * key
  rw [hstep, hexCyclicPred_mid]
  linear_combination (1 - hexOmega ^ 2) * L.lastVertex

theorem HexCyclicLaunch.succ_endsAt
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts) :
    (ofTurns a h0 (ts ++ [-1])).EndsAt
      (labelMid v du (hexCyclicSucc j)) := by
  unfold HexWalk.EndsAt
  rw [hexInfra_endMid_eq_midAccum, hexCyclic_midAccum_append_single]
  exact L.succ_newMid

theorem HexCyclicLaunch.pred_endsAt
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts) :
    (ofTurns a h0 (ts ++ [1])).EndsAt
      (labelMid v du (hexCyclicPred j)) := by
  unfold HexWalk.EndsAt
  rw [hexInfra_endMid_eq_midAccum, hexCyclic_midAccum_append_single]
  exact L.pred_newMid


end
end StatMech.Universality
