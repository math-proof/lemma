/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.HexInfraCut
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part4


namespace StatMech.Universality

open HexWalk List Filter

open scoped BigOperators Real


@[simp] theorem hexW2_prefixBridge_width (h0 : ℤ) (ts : List ℤ) (hone) :
    (hexW2_prefixBridge h0 ts hone).width = hexW2_cutWidth h0 ts := rfl

@[simp] theorem hexW2_prefixBridge_content (h0 : ℤ) (ts : List ℤ) (hone) :
    (hexW2_prefixBridge h0 ts hone).content = ts.take (hexW2_cutPos h0 ts) := rfl


theorem hexW2_prefixBridge_reaches_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts))
    (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    hexWall3_ReachesWidth a h0 (hexW2_prefixBridge h0 ts hone).width
        (hexW2_prefixBridge h0 ts hone).content
      ∧ (HexWalk.ofTurns a h0 (hexW2_prefixBridge h0 ts hone).content).IsLegalSAW := by
  refine ⟨?_, ?_⟩
  · rw [hexW2_prefixBridge_width, hexW2_prefixBridge_content]
    exact hexW2_prefix_reachesCutWidth a h0 ts (le_trans zero_le_one hone)
  · rw [hexW2_prefixBridge_content]
    exact hexW2_prefix_legal a h0 ts hleg


theorem hexW2_prefixBridge_mem (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts))
    (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    hexWall3_mem a h0 (hexW2_prefixBridge h0 ts hone).width
      (hexW2_prefixBridge h0 ts hone).content :=
  let hb := hexW2_prefixBridge_reaches_legal a h0 ts hone hleg
  hexWall3_bridge_mem a h0 (hexW2_prefixBridge h0 ts hone) hb.1 hb.2


theorem hexW2_singleRight_partialDisp_one :
    hexW2_partialDisp 0 [(-1 : ℤ)] 1
      = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re := by
  unfold hexW2_partialDisp
  rw [List.take_succ_cons, List.take_zero]
  exact hexInfra_singleRight_stepReSum


theorem hexW2_singleRight_positiveWidth :
    (1 : ℝ) ≤ hexW2_partialDisp 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)]) := by
  have hdisp1 : (1 : ℝ) ≤ hexW2_partialDisp 0 [(-1 : ℤ)] 1 := by
    rw [hexW2_singleRight_partialDisp_one, hexWall3_halfStep_re, hexWall3_halfStep_re]
    have e0 : Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 := by push_cast; ring
    have em1 : Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) := by
      push_cast; ring
    rw [e0, em1, Real.cos_neg, Real.cos_pi_div_six]
    have hs3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := by
      rw [show (4 : ℝ) / 3 = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [hs3]
  have hmax := hexW2_cutPos_max 0 [(-1 : ℤ)] 1 (by simp)
  linarith


theorem hexW2_singleRight_cutPos_pos :
    0 < hexW2_cutPos 0 [(-1 : ℤ)] :=
  hexW2_cutPos_pos 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth


theorem hexW2_singleRight_prefixBridge_mem (a : ℂ) :
    hexWall3_mem a 0
      (hexW2_prefixBridge 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth).width
      (hexW2_prefixBridge 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth).content :=
  hexW2_prefixBridge_mem a 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth
    (hexWall3_isLegalSAW_witness a)


end StatMech.Universality
