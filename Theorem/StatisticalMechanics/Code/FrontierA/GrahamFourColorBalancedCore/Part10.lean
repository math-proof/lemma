/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part11
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem rowClass_balancedSwap_zero {m X Y : Finset ι} {c : ↑m → Fin 4}
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
    rowClass m (balancedSwap m X Y c) 0 = rowClass m c 0 ∆ (X ∪ Y) := by
  have hY' : Y ⊆ colorClass m (middleSwapOn m X c) 0 ∪
      colorClass m (middleSwapOn m X c) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  unfold balancedSwap
  rw [rowClass_zero, colorClass_outerSwapOn_zero m Y _ hY',
    colorClass_outerSwapOn_one, colorClass_middleSwapOn_zero,
    colorClass_middleSwapOn_one m X c hX, rowClass_zero]
  ext i
  by_cases hiX : i ∈ X
  · rcases Finset.mem_union.mp (hX hiX) with hi1 | hi2
    · have hi0 : i ∉ colorClass m c 0 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (1 : Fin 4) ≠ 0 by decide))) hi1
      have hi2' : i ∉ colorClass m c 2 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (1 : Fin 4) ≠ 2 by decide))) hi1
      have hi3 : i ∉ colorClass m c 3 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (1 : Fin 4) ≠ 3 by decide))) hi1
      have hiY : i ∉ Y := by
        intro hiY
        rcases Finset.mem_union.mp (hY hiY) with h | h
        · exact hi0 h
        · exact hi3 h
      simp [Finset.mem_symmDiff, hiX, hiY, hi0, hi1]
    · have hi0 : i ∉ colorClass m c 0 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (2 : Fin 4) ≠ 0 by decide))) hi2
      have hi1 : i ∉ colorClass m c 1 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (2 : Fin 4) ≠ 1 by decide))) hi2
      have hi3 : i ∉ colorClass m c 3 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (2 : Fin 4) ≠ 3 by decide))) hi2
      have hiY : i ∉ Y := by
        intro hiY
        rcases Finset.mem_union.mp (hY hiY) with h | h
        · exact hi0 h
        · exact hi3 h
      simp [Finset.mem_symmDiff, hiX, hiY, hi0, hi1]
  · by_cases hiY : i ∈ Y
    · rcases Finset.mem_union.mp (hY hiY) with hi0 | hi3
      · have hi1 : i ∉ colorClass m c 1 :=
          (Finset.disjoint_left.mp
            (colorClass_disjoint m c (show (0 : Fin 4) ≠ 1 by decide))) hi0
        simp [Finset.mem_symmDiff, hiX, hiY, hi0, hi1]
      · have hi0 : i ∉ colorClass m c 0 :=
          (Finset.disjoint_left.mp
            (colorClass_disjoint m c (show (3 : Fin 4) ≠ 0 by decide))) hi3
        have hi1 : i ∉ colorClass m c 1 :=
          (Finset.disjoint_left.mp
            (colorClass_disjoint m c (show (3 : Fin 4) ≠ 1 by decide))) hi3
        simp [Finset.mem_symmDiff, hiX, hiY, hi0, hi1]
    · simp [Finset.mem_symmDiff, hiX, hiY]


theorem rowClass_one_eq_sdiff (m : Finset ι) (c : ↑m → Fin 4) :
    rowClass m c 1 = m \ rowClass m c 0 := by
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    have him : (im : ι) = i := rfl
    have hc : c im = 0 ∨ c im = 1 ∨ c im = 2 ∨ c im = 3 := by
      omega
    simp only [rowClass_zero, rowClass_one, Finset.mem_union, Finset.mem_sdiff, hi, true_and]
    simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach]
    simp only [← him]
    aesop
  · have hca : ∀ a : Fin 4, i ∉ colorClass m c a := by
      intro a hmem
      exact hi (colorClass_subset m c a hmem)
    simp [rowClass_zero, rowClass_one, hi, hca]


end FourColor
end GrahamGHS
end StatMech
