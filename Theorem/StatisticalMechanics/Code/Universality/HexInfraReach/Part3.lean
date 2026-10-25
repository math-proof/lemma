/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Def.StatisticalMechanics.Code.Universality.HexInfraReach.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


@[simp] theorem hexInfra_dispBridgeOfContent_content (h0 : ℤ) (ts : List ℤ) (hne hpos) :
    (hexInfra_dispBridgeOfContent h0 ts hne hpos).content = ts := rfl

@[simp] theorem hexInfra_dispBridgeOfContent_width (h0 : ℤ) (ts : List ℤ) (hne hpos) :
    (hexInfra_dispBridgeOfContent h0 ts hne hpos).width = ⌊hexInfra_disp h0 ts⌋₊ := rfl


theorem hexInfra_dispBridgeOfContent_isDispBridge (h0 : ℤ) (ts : List ℤ) (hne hpos)
    (hd : 0 ≤ hexInfra_disp h0 ts) :
    hexInfra_IsDispBridge h0 (hexInfra_dispBridgeOfContent h0 ts hne hpos) := by
  unfold hexInfra_IsDispBridge
  rw [hexInfra_dispBridgeOfContent_width, hexInfra_dispBridgeOfContent_content]
  exact Nat.floor_le hd


theorem hexInfra_dispBridgeOfContent_reaches (a : ℂ) (h0 : ℤ) (ts : List ℤ) (hne hpos)
    (hd : 0 ≤ hexInfra_disp h0 ts) :
    hexWall3_ReachesWidth a h0
      (hexInfra_dispBridgeOfContent h0 ts hne hpos).width
      (hexInfra_dispBridgeOfContent h0 ts hne hpos).content :=
  hexInfra_reachesWidth_of_dispBridge a h0 (hexInfra_dispBridgeOfContent h0 ts hne hpos)
    (hexInfra_dispBridgeOfContent_isDispBridge h0 ts hne hpos hd)


theorem hexInfra_disp_singleRight :
    hexInfra_disp 0 [(-1 : ℤ)] = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re :=
  hexInfra_singleRight_stepReSum


theorem hexInfra_disp_singleRight_ge_one : (1 : ℝ) ≤ hexInfra_disp 0 [(-1 : ℤ)] := by
  rw [hexInfra_disp_singleRight, hexWall3_halfStep_re, hexWall3_halfStep_re]
  have e0 : Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 := by push_cast; ring
  have em1 : Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) := by push_cast; ring
  rw [e0, em1, Real.cos_neg, Real.cos_pi_div_six]
  have hs3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := by
    rw [show (4 : ℝ) / 3 = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [hs3]


theorem hexInfra_disp_singleRight_lt_two : hexInfra_disp 0 [(-1 : ℤ)] < 2 := by
  rw [hexInfra_disp_singleRight, hexWall3_halfStep_re, hexWall3_halfStep_re]
  have e0 : Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 := by push_cast; ring
  have em1 : Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) := by push_cast; ring
  rw [e0, em1, Real.cos_neg, Real.cos_pi_div_six]
  have hs3 : Real.sqrt 3 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [hs3]


theorem hexInfra_floor_disp_singleRight : ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊ = 1 := by
  have hle : (1 : ℝ) ≤ hexInfra_disp 0 [(-1 : ℤ)] := hexInfra_disp_singleRight_ge_one
  have hlt : hexInfra_disp 0 [(-1 : ℤ)] < 2 := hexInfra_disp_singleRight_lt_two
  rw [Nat.floor_eq_iff (by linarith)]
  exact ⟨by push_cast; linarith, by push_cast; linarith⟩


end StatMech.Universality
