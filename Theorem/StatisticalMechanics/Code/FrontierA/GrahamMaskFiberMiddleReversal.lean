/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
import Instance.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem fourColorMaskProfile_middleSwap
    (m : Finset I) (c : ↑m -> Fin 4) :
    fourColorMaskProfile m (middleSwap m c) =
      fourColorMaskProfile m c := by
  apply Prod.ext
  · simp [fourColorMaskProfile, middleMask, colorClass_middleSwap,
      Equiv.swap_apply_def, Finset.union_comm]
  · simp [fourColorMaskProfile, outerMask, colorClass_middleSwap,
      Equiv.swap_apply_def]


theorem rowClass_middleSwap_zero_eq_symmDiff_middleMask
    (m : Finset I) (c : ↑m -> Fin 4) :
    rowClass m (middleSwap m c) 0 =
      rowClass m c 0 ∆ middleMask m c := by
  ext i
  by_cases hi : i ∈ m
  · obtain ⟨a, ha⟩ : ∃ a : ↑m, (a : I) = i :=
      ⟨⟨i, hi⟩, rfl⟩
    subst i
    have hc : c a = 0 ∨ c a = 1 ∨ c a = 2 ∨ c a = 3 := by omega
    rcases hc with hc | hc | hc | hc <;>
      simp [rowClass_zero, middleMask, colorClass_middleSwap,
        Equiv.swap_apply_def, subtype_mem_colorClass_iff, hc,
        Finset.mem_symmDiff]
  · have hclasses : ∀ b : Fin 4, i ∉ colorClass m c b := by
      intro b hib
      exact hi (colorClass_subset m c b hib)
    have hswapclasses : ∀ b : Fin 4,
        i ∉ colorClass m (middleSwap m c) b := by
      intro b hib
      exact hi (colorClass_subset m (middleSwap m c) b hib)
    simp [rowClass_zero, middleMask, hclasses, hswapclasses,
      Finset.mem_symmDiff]


theorem rightSourcePattern_middleSwap_iff_leftSourcePattern
    (ends : I -> Sym2 W) (m : Finset I) (A B : Finset W)
    (c : ↑m -> Fin 4) :
    RightSourcePattern ends m A B (middleSwap m c) ↔
      LeftSourcePattern ends m A B c := by
  simp [RightSourcePattern, LeftSourcePattern, colorClass_middleSwap,
    Equiv.swap_apply_def] <;> tauto


theorem leftSourcePattern_middleSwap_iff_rightSourcePattern
    (ends : I -> Sym2 W) (m : Finset I) (A B : Finset W)
    (c : ↑m -> Fin 4) :
    LeftSourcePattern ends m A B (middleSwap m c) ↔
      RightSourcePattern ends m A B c := by
  simp [RightSourcePattern, LeftSourcePattern, colorClass_middleSwap,
    Equiv.swap_apply_def] <;> tauto


end StatMech.GrahamGHS.FourColor
