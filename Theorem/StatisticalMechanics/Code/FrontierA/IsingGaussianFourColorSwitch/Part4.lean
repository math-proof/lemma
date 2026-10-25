/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part3
open Finset
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


theorem finiteTreeSourceComponentTransfer_spec
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    finiteTreeSourceComponentTransfer ends U k c ⊆
        finiteTreeMiddleUnion U c ∧
      sources ends (finiteTreeSourceComponentTransfer ends U k c) = {k, l} ∧
      (∀ e ∈ finiteTreeSourceComponentTransfer ends U k c,
        ∀ x ∈ ends e,
          connK ends (finiteTreeSourceComponentTransfer ends U k c) k x) := by
  have hconn : connK ends (colorClass U c 1) k l :=
    StatMech.Walls.gc6_pairingPath_abstract ends
      (colorClass U c 1) (colorClass U c 1)
      (fun e he => hloop e (colorClass_subset U c 1 he))
      Finset.Subset.rfl hmix.2.1 hkl
  have hsrc : sources ends
      (edgeComponent ends (colorClass U c 1) k) = {k, l} := by
    rw [sources_edgeComponent, hmix.2.1]
    apply Finset.inter_eq_left.mpr
    intro x hx
    rw [mem_compOf]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hconn
  unfold finiteTreeSourceComponentTransfer
  refine ⟨?_, hsrc, edgeComponent_endpoint_connK ends
    (colorClass U c 1) k⟩
  exact (edgeComponent_subset_edges ends (colorClass U c 1) k).trans
    Finset.subset_union_left


theorem finiteTree_sourceComponentSwitch_separatedSources
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    FiniteTreeSeparatedSources ends U i j k l
      (middleSwapOn U (finiteTreeSourceComponentTransfer ends U k c) c) := by
  have hs := finiteTreeSourceComponentTransfer_spec
    ends U c hloop hkl hmix
  unfold FiniteTreeSeparatedSources
  rw [colorClass_middleSwapOn_zero,
    colorClass_middleSwapOn_one U _ c hs.1,
    colorClass_middleSwapOn_two U _ c hs.1,
    colorClass_middleSwapOn_three,
    sources_symmDiff, sources_symmDiff,
    hmix.1, hmix.2.1, hmix.2.2.1, hmix.2.2.2.1, hs.2.1]
  simp


theorem finiteTree_sourceComponentSwitch_hasCommonVertex
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    ∃ y,
      connK ends
          (colorClass U
              (middleSwapOn U
                (finiteTreeSourceComponentTransfer ends U k c) c) 0 ∪
            colorClass U
              (middleSwapOn U
                (finiteTreeSourceComponentTransfer ends U k c) c) 1) i y ∧
      connK ends
          (colorClass U
              (middleSwapOn U
                (finiteTreeSourceComponentTransfer ends U k c) c) 2 ∪
            colorClass U
              (middleSwapOn U
                (finiteTreeSourceComponentTransfer ends U k c) c) 3) k y := by
  let X := finiteTreeSourceComponentTransfer ends U k c
  have hs := finiteTreeSourceComponentTransfer_spec
    ends U c hloop hkl hmix
  have hX1 : X ⊆ colorClass U c 1 := by
    exact edgeComponent_subset_edges ends (colorClass U c 1) k
  have hmeet := exists_connK_sdiff_meets_of_edgeConnected ends
    (colorClass U c 0 ∪ colorClass U c 1) X i k hs.2.2
    hmix.2.2.2.2
  have hrow0 : (colorClass U c 0 ∪ colorClass U c 1) \ X ⊆
      colorClass U (middleSwapOn U X c) 0 ∪
        colorClass U (middleSwapOn U X c) 1 := by
    intro e he
    rcases Finset.mem_sdiff.mp he with ⟨he01, heX⟩
    rcases Finset.mem_union.mp he01 with he0 | he1
    · rw [colorClass_middleSwapOn_zero]
      exact Finset.mem_union_left _ he0
    · apply Finset.mem_union_right
      rw [colorClass_middleSwapOn_one U X c hs.1]
      exact Finset.mem_symmDiff.mpr (Or.inl ⟨he1, heX⟩)
  have hrow1 : X ⊆
      colorClass U (middleSwapOn U X c) 2 ∪
        colorClass U (middleSwapOn U X c) 3 := by
    intro e heX
    apply Finset.mem_union_left
    rw [colorClass_middleSwapOn_two U X c hs.1]
    apply Finset.mem_symmDiff.mpr
    exact Or.inr ⟨heX, fun he2 =>
      Finset.disjoint_left.mp
        (colorClass_disjoint U c (show (1 : Fin 4) ≠ 2 by decide))
        (hX1 heX) he2⟩
  obtain ⟨y, hiy, hky⟩ := hmeet
  exact ⟨y, connK_mono hrow0 hiy, connK_mono hrow1 hky⟩


end StatMech.FrontierA
