/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaComponentReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaGhostComponent.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


omit [Fintype V] in
theorem mem_lpReplicaPartialReflectSource
    (A C : Finset (LPReplicaCurrentVertex V))
    (x : LPReplicaCurrentVertex V) :
    x ∈ lpReplicaPartialReflectSource A C ↔
      ((x ∈ A ∧ x ∉ C) ∧
          ¬ (lpReplicaCurrentReflect x ∈ A ∧
            lpReplicaCurrentReflect x ∈ C)) ∨
        ((lpReplicaCurrentReflect x ∈ A ∧
            lpReplicaCurrentReflect x ∈ C) ∧
          ¬ (x ∈ A ∧ x ∉ C)) := by
  have hinv : Function.Involutive
      (lpReplicaCurrentReflect : LPReplicaCurrentVertex V ->
        LPReplicaCurrentVertex V) := by
    intro z
    rcases z with (z | b)
    · rcases z with z | z <;> rfl
    · cases b <;> rfl
  unfold lpReplicaPartialReflectSource
  simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_inter,
    Finset.mem_map]
  constructor
  · rintro (⟨hx, hnot⟩ | ⟨hmap, hx⟩)
    · left
      refine ⟨hx, ?_⟩
      rintro ⟨hra, hrc⟩
      apply hnot
      refine ⟨lpReplicaCurrentReflect x, ⟨hra, hrc⟩, ?_⟩
      exact hinv x
    · right
      rcases hmap with ⟨y, hy, rfl⟩
      refine ⟨?_, hx⟩
      change lpReplicaCurrentReflect (lpReplicaCurrentReflect y) ∈ A ∧
        lpReplicaCurrentReflect (lpReplicaCurrentReflect y) ∈ C
      simpa only [hinv y] using hy
  · rintro (⟨hx, hnot⟩ | ⟨hr, hx⟩)
    · left
      refine ⟨hx, ?_⟩
      rintro ⟨y, hy, hxy⟩
      apply hnot
      subst x
      change lpReplicaCurrentReflect (lpReplicaCurrentReflect y) ∈ A ∧
        lpReplicaCurrentReflect (lpReplicaCurrentReflect y) ∈ C
      simpa only [hinv y] using hy
    · right
      refine ⟨?_, hx⟩
      refine ⟨lpReplicaCurrentReflect x, ?_, ?_⟩
      · simpa only [hinv x] using hr
      · exact hinv x

omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem lpReplicaPartial_six_eq_seam_j
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j : I} (hij : i ≠ j)
    (C : Finset (LPReplicaCurrentVertex V))
    (hg0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ C)
    (hg1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ C)
    (hsplitI :
      (lpReplicaCurrentLeft sites i ∈ C ∧
          lpReplicaCurrentRight sites i ∉ C) ∨
        (lpReplicaCurrentLeft sites i ∉ C ∧
          lpReplicaCurrentRight sites i ∈ C))
    (hnotSplitJ : ¬ (
      (lpReplicaCurrentLeft sites j ∈ C ∧
          lpReplicaCurrentRight sites j ∉ C) ∨
        (lpReplicaCurrentLeft sites j ∉ C ∧
          lpReplicaCurrentRight sites j ∈ C))) :
    lpReplicaPartialReflectSource
        {lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
          lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i,
          lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} C =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j := by
  have hs : sites i ≠ sites j := hsite.ne hij
  ext z
  rw [mem_lpReplicaPartialReflectSource]
  by_cases hli : lpReplicaCurrentLeft sites i ∈ C <;>
    by_cases hri : lpReplicaCurrentRight sites i ∈ C <;>
    by_cases hlj : lpReplicaCurrentLeft sites j ∈ C <;>
    by_cases hrj : lpReplicaCurrentRight sites j ∈ C
  all_goals
    rcases z with (z | b)
    · rcases z with x | x <;>
        simp only [lpReplicaCurrentReflect_left,
          lpReplicaCurrentReflect_right] <;>
        by_cases hi : x = sites i <;> by_cases hj : x = sites j <;>
          simp_all [lpMatchingSeamSource, lpReplicaCurrentLeft,
            lpReplicaCurrentRight, lpReplicaCurrentGhost0,
            lpReplicaCurrentGhost1, Finset.mem_symmDiff]
    · cases b <;>
        simp_all [lpMatchingSeamSource, lpReplicaCurrentLeft,
          lpReplicaCurrentRight, lpReplicaCurrentGhost0,
          lpReplicaCurrentGhost1, Finset.mem_symmDiff]

omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem lpReplicaPartial_six_eq_seam_i
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j : I} (hij : i ≠ j)
    (C : Finset (LPReplicaCurrentVertex V))
    (hg0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ C)
    (hg1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ C)
    (hnotSplitI : ¬ (
      (lpReplicaCurrentLeft sites i ∈ C ∧
          lpReplicaCurrentRight sites i ∉ C) ∨
        (lpReplicaCurrentLeft sites i ∉ C ∧
          lpReplicaCurrentRight sites i ∈ C)))
    (hsplitJ :
      (lpReplicaCurrentLeft sites j ∈ C ∧
          lpReplicaCurrentRight sites j ∉ C) ∨
        (lpReplicaCurrentLeft sites j ∉ C ∧
          lpReplicaCurrentRight sites j ∈ C)) :
    lpReplicaPartialReflectSource
        {lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
          lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i,
          lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} C =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
  have hs : sites i ≠ sites j := hsite.ne hij
  ext z
  rw [mem_lpReplicaPartialReflectSource]
  by_cases hli : lpReplicaCurrentLeft sites i ∈ C <;>
    by_cases hri : lpReplicaCurrentRight sites i ∈ C <;>
    by_cases hlj : lpReplicaCurrentLeft sites j ∈ C <;>
    by_cases hrj : lpReplicaCurrentRight sites j ∈ C
  all_goals
    rcases z with (z | b)
    · rcases z with x | x <;>
        simp only [lpReplicaCurrentReflect_left,
          lpReplicaCurrentReflect_right] <;>
        by_cases hi : x = sites i <;> by_cases hj : x = sites j <;>
          simp_all [lpMatchingSeamSource, lpReplicaCurrentLeft,
            lpReplicaCurrentRight, lpReplicaCurrentGhost0,
            lpReplicaCurrentGhost1, Finset.mem_symmDiff]
    · cases b <;>
        simp_all [lpMatchingSeamSource, lpReplicaCurrentLeft,
          lpReplicaCurrentRight, lpReplicaCurrentGhost0,
          lpReplicaCurrentGhost1, Finset.mem_symmDiff]

end
end StatMech.Ising
