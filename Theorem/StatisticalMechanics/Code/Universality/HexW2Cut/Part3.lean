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
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part3


namespace StatMech.Universality

open HexWalk List Filter

open scoped BigOperators Real


theorem hexW2_prefix_reachesCutWidth (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hnn : 0 ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    hexWall3_ReachesWidth a h0 (hexW2_cutWidth h0 ts) (ts.take (hexW2_cutPos h0 ts)) :=
  hexW2_prefix_reachesWidth a h0 (hexW2_cutWidth h0 ts) ts (Nat.floor_le hnn)


theorem hexW2_cutWidth_pos (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    0 < hexW2_cutWidth h0 ts := by
  rw [hexW2_cutWidth, Nat.floor_pos]; exact hone


theorem hexW2_prefix_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    (HexWalk.ofTurns a h0 (ts.take (hexW2_cutPos h0 ts))).IsLegalSAW :=
  hexCut_legal_take a h0 ts (hexW2_cutPos h0 ts) hleg


theorem hexW2_suffix_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    (HexWalk.ofTurns (hexDropMid a h0 ts (hexW2_cutPos h0 ts))
        (h0 + (ts.take (hexW2_cutPos h0 ts)).sum)
        (ts.drop (hexW2_cutPos h0 ts))).IsLegalSAW :=
  hexCut_legal_drop a h0 ts (hexW2_cutPos h0 ts) (hexW2_cutPos_le h0 ts) hleg


theorem hexW2_displacement_split (h0 : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h0 ts
      = hexInfra_stepReSum h0 (ts.take (hexW2_cutPos h0 ts))
        + hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take (hexW2_cutPos h0 ts)))
            (ts.drop (hexW2_cutPos h0 ts)) :=
  hexInfra_stepReSum_take_drop h0 ts (hexW2_cutPos h0 ts)


theorem hexW2_partialDisp_zero (h0 : ℤ) (ts : List ℤ) :
    hexW2_partialDisp h0 ts 0 = (HexWalk.halfStep h0).re := by
  unfold hexW2_partialDisp
  simp


theorem hexW2_cutPos_pos (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    0 < hexW2_cutPos h0 ts := by
  rcases Nat.eq_zero_or_pos (hexW2_cutPos h0 ts) with hcp0 | hpos
  swap
  · exact hpos
  exfalso
  rw [hcp0] at hone
  rw [hexW2_partialDisp_zero] at hone
  have hhalf : (HexWalk.halfStep h0).re ≤ 1 / 2 := hexInfra_halfStep_re_le h0
  linarith


theorem hexW2_prefix_content_ne (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    ts.take (hexW2_cutPos h0 ts) ≠ [] := by
  have hpos := hexW2_cutPos_pos h0 ts hone
  have hcple := hexW2_cutPos_le h0 ts
  intro hnil
  rw [List.take_eq_nil_iff] at hnil
  rcases hnil with h | h
  · omega
  · subst h; simp at hcple; omega


end StatMech.Universality
