/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInfraReach.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Def.StatisticalMechanics.Code.Universality.HexW3Link.Part3


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


@[simp] theorem hexW3_witnessBridge_content : hexW3_witnessBridge.content = [(-1 : ℤ)] := rfl

@[simp] theorem hexW3_witnessBridge_width : hexW3_witnessBridge.width = 1 := by
  change ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊ = 1
  rw [hexInfra_floor_disp_singleRight]


theorem hexW3_witness_isDispBridge :
    hexInfra_IsDispBridge 0 hexW3_witnessBridge :=
  hexW3_anchor_isDispBridge 0 hexWall3_witnessBridge _
    (by change 0 ≤ hexInfra_disp 0 [(-1 : ℤ)]
        exact le_trans (by norm_num) hexInfra_disp_singleRight_ge_one)


theorem hexW3_witness_reaches (a : ℂ) :
    hexWall3_ReachesWidth a 0 hexW3_witnessBridge.width hexW3_witnessBridge.content :=
  hexInfra_reachesWidth_of_dispBridge a 0 hexW3_witnessBridge hexW3_witness_isDispBridge


theorem hexW3_witnessRung_wf : hexHW_WF [((1 : ℕ), (-1 : ℤ))] := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp; exact one_pos


theorem hexW3_witnessRung_decomp :
    bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf
      = [(⟨1, one_pos, [(-1 : ℤ)], by simp⟩ : HexBridge)] := by
  rw [bridgeDecomp_cons ((1 : ℕ), (-1 : ℤ)) [] hexW3_witnessRung_wf]
  have hdrop : hexHW_dropRun ((1 : ℕ), (-1 : ℤ)) [] = [] := by
    simp [hexHW_dropRun]
  have hwfnil : hexHW_WF ([] : List (ℕ × ℤ)) := fun p hp => absurd hp (by simp)
  have htail : bridgeDecomp (hexHW_dropRun ((1 : ℕ), (-1 : ℤ)) [])
      (hexHW_WF_dropRun ((1 : ℕ), (-1 : ℤ)) [] hexW3_witnessRung_wf) = [] := by
    rw [bridgeDecomp_congr (hexHW_dropRun ((1 : ℕ), (-1 : ℤ)) []) []
      (hexHW_WF_dropRun ((1 : ℕ), (-1 : ℤ)) [] hexW3_witnessRung_wf) hwfnil hdrop]
    exact bridgeDecomp_nil _
  rw [htail]
  congr 1


theorem hexW3_witnessRung_hPos :
    ∀ b ∈ bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf,
      0 < ⌊hexInfra_disp 0 b.content⌋₊ := by
  rw [hexW3_witnessRung_decomp]
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb
  change 0 < ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊
  rw [hexInfra_floor_disp_singleRight]; exact one_pos


theorem hexW3_witnessRung_hD :
    ∀ b ∈ bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf,
      0 ≤ hexInfra_disp 0 b.content := by
  rw [hexW3_witnessRung_decomp]
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb
  change 0 ≤ hexInfra_disp 0 [(-1 : ℤ)]
  exact le_trans (by norm_num) hexInfra_disp_singleRight_ge_one


theorem hexW3_witnessRung_dispBridge_nonempty_anchored :
    (hexW3_dispBridgeDecomp 0 [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf
        hexW3_witnessRung_hPos) ≠ []
      ∧ ∀ b' ∈ hexW3_dispBridgeDecomp 0 [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf
          hexW3_witnessRung_hPos, hexInfra_IsDispBridge 0 b' := by
  refine ⟨?_, hexW3_bridgeDecomp_isDispBridge 0 [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf
    hexW3_witnessRung_hPos hexW3_witnessRung_hD⟩
  simp only [hexW3_dispBridgeDecomp, ne_eq, List.map_eq_nil_iff, List.attach_eq_nil_iff]
  rw [hexW3_witnessRung_decomp]
  exact List.cons_ne_nil _ _

end StatMech.Universality
