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
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part8
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem outerSwapOn_involutive (m Y : Finset ι) (c : ↑m → Fin 4) :
    outerSwapOn m Y (outerSwapOn m Y c) = c := by
  funext i
  by_cases hi : (i : ι) ∈ Y <;> simp [outerSwapOn, hi]

theorem colorClass_outerSwapOn_one (m Y : Finset ι) (c : ↑m → Fin 4) :
    colorClass m (outerSwapOn m Y c) 1 = colorClass m c 1 := by
  have hswap : ∀ x : Fin 4, Equiv.swap (0 : Fin 4) 3 x = 1 ↔ x = 1 := by
    intro x
    rw [← show Equiv.swap (0 : Fin 4) 3 1 = 1 by decide]
    exact Equiv.apply_eq_iff_eq _
  ext i
  by_cases hi : i ∈ m
  · by_cases hiY : i ∈ Y <;> simp [colorClass, outerSwapOn, hi, hiY, hswap]
  · simp [colorClass, hi]

theorem colorClass_outerSwapOn_two (m Y : Finset ι) (c : ↑m → Fin 4) :
    colorClass m (outerSwapOn m Y c) 2 = colorClass m c 2 := by
  have hswap : ∀ x : Fin 4, Equiv.swap (0 : Fin 4) 3 x = 2 ↔ x = 2 := by
    intro x
    rw [← show Equiv.swap (0 : Fin 4) 3 2 = 2 by decide]
    exact Equiv.apply_eq_iff_eq _
  ext i
  by_cases hi : i ∈ m
  · by_cases hiY : i ∈ Y <;> simp [colorClass, outerSwapOn, hi, hiY, hswap]
  · simp [colorClass, hi]

theorem colorClass_outerSwapOn_zero (m Y : Finset ι) (c : ↑m → Fin 4)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
    colorClass m (outerSwapOn m Y c) 0 = colorClass m c 0 ∆ Y := by
  ext i
  by_cases hi : i ∈ m
  · by_cases hiY : i ∈ Y
    · have hout := hY hiY
      simp only [Finset.mem_union] at hout
      simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hout
      simp only [Finset.mem_symmDiff]
      simp [colorClass, outerSwapOn, Equiv.swap_apply_def, hi, hiY] at hout ⊢
      aesop
    · simp [colorClass, outerSwapOn, hi, hiY, Finset.mem_symmDiff]
  · have hiY : i ∉ Y := by
      intro h
      rcases Finset.mem_union.mp (hY h) with h0 | h3
      · exact hi (colorClass_subset m c 0 h0)
      · exact hi (colorClass_subset m c 3 h3)
    simp [colorClass, hi, hiY, Finset.mem_symmDiff]

theorem colorClass_outerSwapOn_three (m Y : Finset ι) (c : ↑m → Fin 4)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
    colorClass m (outerSwapOn m Y c) 3 = colorClass m c 3 ∆ Y := by
  ext i
  by_cases hi : i ∈ m
  · by_cases hiY : i ∈ Y
    · have hout := hY hiY
      simp only [Finset.mem_union] at hout
      simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hout
      simp only [Finset.mem_symmDiff]
      simp [colorClass, outerSwapOn, Equiv.swap_apply_def, hi, hiY] at hout ⊢
      aesop
    · simp [colorClass, outerSwapOn, hi, hiY, Finset.mem_symmDiff]
  · have hiY : i ∉ Y := by
      intro h
      rcases Finset.mem_union.mp (hY h) with h0 | h3
      · exact hi (colorClass_subset m c 0 h0)
      · exact hi (colorClass_subset m c 3 h3)
    simp [colorClass, hi, hiY, Finset.mem_symmDiff]


end FourColor
end GrahamGHS
end StatMech
