/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch
open Finset
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


theorem finiteTreeMiddleTransfer_spec
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4)
    (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
    FiniteTreeMiddleTransferWitness ends U k l c
      (finiteTreeMiddleTransfer ends U k l c) := by
  unfold finiteTreeMiddleTransfer
  unfold finiteTreeMiddleTransferFromUnion
  unfold FiniteTreeMiddleTransferWitness at h ⊢
  rw [dif_pos h]
  exact Classical.choose_spec h


theorem finiteTreeMiddleUnion_middleSwapOn
    (U X : Finset ι) (c : ↑U -> Fin 4)
    (hX : X ⊆ finiteTreeMiddleUnion U c) :
    finiteTreeMiddleUnion U (middleSwapOn U X c) =
      finiteTreeMiddleUnion U c := by
  unfold finiteTreeMiddleUnion at hX ⊢
  rw [colorClass_middleSwapOn_one U X c hX,
    colorClass_middleSwapOn_two U X c hX]
  ext e
  have he := @hX e
  have hd : Disjoint (colorClass U c 1) (colorClass U c 2) :=
    colorClass_disjoint U c (by decide)
  rw [Finset.disjoint_left] at hd
  by_cases he1 : e ∈ colorClass U c 1 <;>
    by_cases he2 : e ∈ colorClass U c 2 <;>
    by_cases heX : e ∈ X <;>
    simp_all [Finset.mem_union, Finset.mem_symmDiff]

theorem finiteTreeMiddleTransferWitness_middleSwapOn_iff
    (ends : ι -> Sym2 V) (U X Y : Finset ι) (k l : V)
    (c : ↑U -> Fin 4)
    (hX : X ⊆ finiteTreeMiddleUnion U c) :
    FiniteTreeMiddleTransferWitness ends U k l
        (middleSwapOn U X c) Y ↔
      FiniteTreeMiddleTransferWitness ends U k l c Y := by
  unfold FiniteTreeMiddleTransferWitness
  rw [finiteTreeMiddleUnion_middleSwapOn U X c hX]


theorem finiteTreeMiddleTransfer_selected_invariant
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4)
    (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
    finiteTreeMiddleTransfer ends U k l
        (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) =
      finiteTreeMiddleTransfer ends U k l c := by
  have hspec := finiteTreeMiddleTransfer_spec ends U k l c h
  have hsub := hspec.1
  have hu := finiteTreeMiddleUnion_middleSwapOn U
    (finiteTreeMiddleTransfer ends U k l c) c hsub
  exact congrArg (fun M => finiteTreeMiddleTransferFromUnion ends M k l) hu


end StatMech.FrontierA
