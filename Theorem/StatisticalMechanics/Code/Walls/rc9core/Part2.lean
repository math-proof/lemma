/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc8core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Walls.rc9core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc9_deficitBridge_of_residue (h : rc9_DeficitBridgeResidue) : rc7_DeficitBridge := by
  intro n A B
  by_cases hopp : (IsIncreasing A ∧ IsDecreasing B) ∨ (IsDecreasing A ∧ IsIncreasing B)
  · rcases hopp with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact rc8_deficit_le_zero_inc_dec hA hB
    · exact rc8_deficit_le_zero_dec_inc hA hB
  · by_cases hdd : IsDecreasing A ∧ IsDecreasing B
    · 
      apply rc9_deficit_le_of_flip
      set A' := flipCfg ⁻¹' A with hA'def
      set B' := flipCfg ⁻¹' B with hB'def
      have hA' : IsIncreasing A' := isIncreasing_flip_preimage hdd.1
      have hB' : IsIncreasing B' := isIncreasing_flip_preimage hdd.2
      by_cases hopp' : (IsIncreasing A' ∧ IsDecreasing B') ∨ (IsDecreasing A' ∧ IsIncreasing B')
      · rcases hopp' with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact rc8_deficit_le_zero_inc_dec ha hb
        · exact rc8_deficit_le_zero_dec_inc ha hb
      · by_cases hdd' : IsDecreasing A' ∧ IsDecreasing B'
        · exact absurd (Or.inl ⟨hA', hdd'.2⟩) hopp'
        · exact h n A' B' hopp' hdd'
    · exact h n A B hopp hdd


theorem rc9_residue_of_deficitBridge (h : rc7_DeficitBridge) : rc9_DeficitBridgeResidue :=
  fun n A B _ _ => h n A B


theorem rc9_residue_iff_deficitBridge : rc7_DeficitBridge ↔ rc9_DeficitBridgeResidue :=
  ⟨rc9_residue_of_deficitBridge, rc9_deficitBridge_of_residue⟩


theorem rc9_residue_iff_nonOpp : rc9_DeficitBridgeResidue ↔ rc8_DeficitBridgeNonOpp :=
  rc9_residue_iff_deficitBridge.symm.trans rc8_deficitBridge_iff_nonOpp


theorem rc9_reimerCardFormAll_of_residue (h : rc9_DeficitBridgeResidue) : ReimerCardFormAll :=
  rc7_reimerCardFormAll_of_deficitBridge (rc9_deficitBridge_of_residue h)


theorem rc9_deficit_swap_rbi : rc5_deficit rbi_A rbi_B = rc5_deficit rbi_B rbi_A :=
  rc9_deficit_swap rbi_A rbi_B


theorem rc9_deficit_flip_rbi :
    rc5_deficit (flipCfg ⁻¹' rbi_A) (flipCfg ⁻¹' rbi_B) = rc5_deficit rbi_A rbi_B :=
  rc9_deficit_flip_invariant rbi_A rbi_B


theorem rc9_deficit_one (A B : Set (ConfigSpace (Fin 1))) : rc5_deficit A B ≤ 0 :=
  rc7_deficit_one A B


theorem rc9_deficit_rbi : rc5_deficit rbi_A rbi_B ≤ 0 :=
  rc7_deficit_rbi


theorem rc9_cardform_symmetry_reduction :
    (∀ A B : Set (ConfigSpace α),
        rc5_deficit (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) = rc5_deficit A B)
      ∧ (∀ A B : Set (ConfigSpace α), rc5_deficit A B = rc5_deficit B A)
      ∧ (rc7_DeficitBridge ↔ rc9_DeficitBridgeResidue)
      ∧ (rc9_DeficitBridgeResidue ↔ rc8_DeficitBridgeNonOpp)
      ∧ (rc9_DeficitBridgeResidue → ReimerCardFormAll) :=
  ⟨rc9_deficit_flip_invariant,
    rc9_deficit_swap,
    rc9_residue_iff_deficitBridge,
    rc9_residue_iff_nonOpp,
    rc9_reimerCardFormAll_of_residue⟩

end StatMech.Walls
