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
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part7
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem middleSwapOn_involutive (m X : Finset ι) (c : ↑m → Fin 4) :
    middleSwapOn m X (middleSwapOn m X c) = c := by
  funext i
  by_cases hi : (i : ι) ∈ X <;> simp [middleSwapOn, hi]

theorem colorClass_middleSwapOn_zero (m X : Finset ι) (c : ↑m → Fin 4) :
    colorClass m (middleSwapOn m X c) 0 = colorClass m c 0 := by
  have hswap : ∀ x : Fin 4, Equiv.swap (1 : Fin 4) 2 x = 0 ↔ x = 0 := by
    intro x
    rw [← show Equiv.swap (1 : Fin 4) 2 0 = 0 by decide]
    exact Equiv.apply_eq_iff_eq _
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    by_cases hiX : i ∈ X <;> simp [colorClass, middleSwapOn, hi, hiX, im, hswap]
  · simp [colorClass, hi]

theorem colorClass_middleSwapOn_three (m X : Finset ι) (c : ↑m → Fin 4) :
    colorClass m (middleSwapOn m X c) 3 = colorClass m c 3 := by
  have hswap : ∀ x : Fin 4, Equiv.swap (1 : Fin 4) 2 x = 3 ↔ x = 3 := by
    intro x
    rw [← show Equiv.swap (1 : Fin 4) 2 3 = 3 by decide]
    exact Equiv.apply_eq_iff_eq _
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    by_cases hiX : i ∈ X <;> simp [colorClass, middleSwapOn, hi, hiX, im, hswap]
  · simp [colorClass, hi]


theorem colorClass_middleSwapOn_one (m X : Finset ι) (c : ↑m → Fin 4)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2) :
    colorClass m (middleSwapOn m X c) 1 = colorClass m c 1 ∆ X := by
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    by_cases hiX : i ∈ X
    · have hmid := hX hiX
      simp only [Finset.mem_union] at hmid
      simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hmid
      simp only [Finset.mem_symmDiff]
      simp [colorClass, middleSwapOn, Equiv.swap_apply_def, hi, hiX, im] at hmid ⊢
      aesop
    · simp [colorClass, middleSwapOn, hi, hiX, im, Finset.mem_symmDiff]
  · have hiX : i ∉ X := by
      intro h
      rcases Finset.mem_union.mp (hX h) with h1 | h2
      · exact hi (colorClass_subset m c 1 h1)
      · exact hi (colorClass_subset m c 2 h2)
    simp [colorClass, hi, hiX, Finset.mem_symmDiff]

theorem colorClass_middleSwapOn_two (m X : Finset ι) (c : ↑m → Fin 4)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2) :
    colorClass m (middleSwapOn m X c) 2 = colorClass m c 2 ∆ X := by
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    by_cases hiX : i ∈ X
    · have hmid := hX hiX
      simp only [Finset.mem_union] at hmid
      simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hmid
      simp only [Finset.mem_symmDiff]
      simp [colorClass, middleSwapOn, Equiv.swap_apply_def, hi, hiX, im] at hmid ⊢
      aesop
    · simp [colorClass, middleSwapOn, hi, hiX, im, Finset.mem_symmDiff]
  · have hiX : i ∉ X := by
      intro h
      rcases Finset.mem_union.mp (hX h) with h1 | h2
      · exact hi (colorClass_subset m c 1 h1)
      · exact hi (colorClass_subset m c 2 h2)
    simp [colorClass, hi, hiX, Finset.mem_symmDiff]


end FourColor
end GrahamGHS
end StatMech
