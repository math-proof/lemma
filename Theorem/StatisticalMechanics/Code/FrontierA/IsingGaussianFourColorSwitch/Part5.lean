/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part4
open Finset
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


theorem finiteTreeInvariantComponentTransfer_spec
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    finiteTreeInvariantComponentTransfer ends U k c ⊆
        finiteTreeMiddleUnion U c ∧
      sources ends (finiteTreeInvariantComponentTransfer ends U k c) = {k, l} ∧
      (∀ e ∈ finiteTreeInvariantComponentTransfer ends U k c,
        ∀ x ∈ ends e,
          connK ends (finiteTreeInvariantComponentTransfer ends U k c) k x) := by
  have hmiddle : sources ends (finiteTreeMiddleUnion U c) = {k, l} := by
    unfold finiteTreeMiddleUnion
    rw [sources_union_of_disjoint
      (colorClass_disjoint U c (show (1 : Fin 4) ≠ 2 by decide)),
      hmix.2.1, hmix.2.2.1]
    simp
  have hconn1 : connK ends (colorClass U c 1) k l :=
    StatMech.Walls.gc6_pairingPath_abstract ends
      (colorClass U c 1) (colorClass U c 1)
      (fun e he => hloop e (colorClass_subset U c 1 he))
      Finset.Subset.rfl hmix.2.1 hkl
  have hconn : connK ends (finiteTreeMiddleUnion U c) k l := by
    exact connK_mono Finset.subset_union_left hconn1
  have hsrc : sources ends
      (edgeComponent ends (finiteTreeMiddleUnion U c) k) = {k, l} := by
    rw [sources_edgeComponent, hmiddle]
    apply Finset.inter_eq_left.mpr
    intro x hx
    rw [mem_compOf]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hconn
  unfold finiteTreeInvariantComponentTransfer
  exact ⟨edgeComponent_subset_edges ends (finiteTreeMiddleUnion U c) k,
    hsrc, edgeComponent_endpoint_connK ends (finiteTreeMiddleUnion U c) k⟩


theorem finiteTreeInvariantComponentTransfer_selected_invariant
    (ends : ι -> Sym2 V) (U : Finset ι) (k : V)
    (c : ↑U -> Fin 4)
    (hsub : finiteTreeInvariantComponentTransfer ends U k c ⊆
      finiteTreeMiddleUnion U c) :
    finiteTreeInvariantComponentTransfer ends U k
        (middleSwapOn U
          (finiteTreeInvariantComponentTransfer ends U k c) c) =
      finiteTreeInvariantComponentTransfer ends U k c := by
  exact congrArg (fun M => edgeComponent ends M k)
    (finiteTreeMiddleUnion_middleSwapOn U
      (finiteTreeInvariantComponentTransfer ends U k c) c hsub)

theorem finiteTree_invariantComponentSwitch_separatedSources
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    FiniteTreeSeparatedSources ends U i j k l
      (middleSwapOn U
        (finiteTreeInvariantComponentTransfer ends U k c) c) := by
  have hs := finiteTreeInvariantComponentTransfer_spec
    ends U c hloop hkl hmix
  unfold FiniteTreeSeparatedSources
  rw [colorClass_middleSwapOn_zero,
    colorClass_middleSwapOn_one U _ c hs.1,
    colorClass_middleSwapOn_two U _ c hs.1,
    colorClass_middleSwapOn_three,
    sources_symmDiff, sources_symmDiff,
    hmix.1, hmix.2.1, hmix.2.2.1, hmix.2.2.2.1, hs.2.1]
  simp

theorem finiteTree_invariantComponentSwitch_involutive
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    middleSwapOn U
        (finiteTreeInvariantComponentTransfer ends U k
          (middleSwapOn U
            (finiteTreeInvariantComponentTransfer ends U k c) c))
        (middleSwapOn U
          (finiteTreeInvariantComponentTransfer ends U k c) c) = c := by
  have hs := finiteTreeInvariantComponentTransfer_spec
    ends U c hloop hkl hmix
  rw [finiteTreeInvariantComponentTransfer_selected_invariant
    ends U k c hs.1]
  exact middleSwapOn_involutive U
    (finiteTreeInvariantComponentTransfer ends U k c) c


theorem finiteTree_selectedSwitch_separatedSources
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    FiniteTreeSeparatedSources ends U i j k l
      (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) := by
  have hex := exists_finiteTreeMiddleTransferWitness_of_mixed
    ends U c hloop hkl hmix
  have hs := finiteTreeMiddleTransfer_spec ends U k l c hex
  unfold FiniteTreeSeparatedSources
  rw [colorClass_middleSwapOn_zero,
    colorClass_middleSwapOn_one U _ c hs.1,
    colorClass_middleSwapOn_two U _ c hs.1,
    colorClass_middleSwapOn_three,
    sources_symmDiff, sources_symmDiff,
    hmix.1, hmix.2.1, hmix.2.2.1, hmix.2.2.2.1, hs.2.1]
  simp


theorem finiteTree_selectedSwitch_involutive
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4)
    (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
    middleSwapOn U
        (finiteTreeMiddleTransfer ends U k l
          (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c))
        (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) = c := by
  rw [finiteTreeMiddleTransfer_selected_invariant ends U k l c h]
  exact middleSwapOn_involutive U
    (finiteTreeMiddleTransfer ends U k l c) c

end StatMech.FrontierA
