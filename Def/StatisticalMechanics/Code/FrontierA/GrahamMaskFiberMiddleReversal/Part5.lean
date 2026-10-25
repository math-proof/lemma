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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def sourceMaskCycleTranslationEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (X Y : Finset I)
    (hX : X ⊆ p.1) (hY : Y ⊆ p.2)
    (hsrcX : sources ends X = ∅) (hsrcY : sources ends Y = ∅) :
    leftSourceMaskFiber ends m j k l zero p ≃
      leftSourceMaskFiber ends m j k l zero p where
  toFun c := by
    have hmiddle : middleMask m c.1 = p.1 :=
      congrArg Prod.fst c.2.2
    have houter : outerMask m c.1 = p.2 :=
      congrArg Prod.snd c.2.2
    have hXc : X ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
      change X ⊆ middleMask m c.1
      rw [hmiddle]
      exact hX
    have hYc : Y ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
      change Y ⊆ outerMask m c.1
      rw [houter]
      exact hY
    exact ⟨balancedSwap m X Y c.1, ⟨
      leftSourcePattern_of_sourceless_balancedSwap c.2.1
        hXc hYc hsrcX hsrcY,
      (fourColorMaskProfile_balancedSwap m X Y c.1).trans c.2.2⟩⟩
  invFun c := by
    have hmiddle : middleMask m c.1 = p.1 :=
      congrArg Prod.fst c.2.2
    have houter : outerMask m c.1 = p.2 :=
      congrArg Prod.snd c.2.2
    have hXc : X ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
      change X ⊆ middleMask m c.1
      rw [hmiddle]
      exact hX
    have hYc : Y ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
      change Y ⊆ outerMask m c.1
      rw [houter]
      exact hY
    exact ⟨balancedSwap m X Y c.1, ⟨
      leftSourcePattern_of_sourceless_balancedSwap c.2.1
        hXc hYc hsrcX hsrcY,
      (fourColorMaskProfile_balancedSwap m X Y c.1).trans c.2.2⟩⟩
  left_inv c := by
    apply Subtype.ext
    exact balancedSwap_involutive m X Y c.1
  right_inv c := by
    apply Subtype.ext
    exact balancedSwap_involutive m X Y c.1


noncomputable def outerCycleSourceMaskEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (Y : Finset I)
    (hY : Y ⊆ p.2) (hsrcY : sources ends Y = ∅) :
    leftSourceMaskFiber ends m j k l zero p ≃
      leftSourceMaskFiber ends m j k l zero p :=
  sourceMaskCycleTranslationEquiv ends m j k l zero p ∅ Y
    (by simp) hY (by simp [sources, degK]) hsrcY


end StatMech.GrahamGHS.FourColor
