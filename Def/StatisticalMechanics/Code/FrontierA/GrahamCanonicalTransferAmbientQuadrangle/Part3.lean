/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalQuadrangleCompletionSourceMap
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    leftSourceMaskFiber ends m j k l zero p := by
  let X := canonicalMiddleTransferDifference ends m k zero a.1.1 b.1.1
  let Y := canonicalOuterTransferDifference ends m k zero a.1.1 b.1.1
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1
  have hva := canonicalTransfers_valid hloop hjk hkl a.1.2
  have hvb := canonicalTransfers_valid hloop hjk hkl b.1.2
  have haProfile : fourColorMaskProfile m a.1.1 =
      fourColorMaskProfile m c.1 := a.2.trans c.2.2.symm
  have hbProfile : fourColorMaskProfile m b.1.1 =
      fourColorMaskProfile m c.1 := b.2.trans c.2.2.symm
  have haMid : middleMask m a.1.1 = middleMask m c.1 :=
    congrArg Prod.fst haProfile
  have hbMid : middleMask m b.1.1 = middleMask m c.1 :=
    congrArg Prod.fst hbProfile
  have haOut : outerMask m a.1.1 = outerMask m c.1 :=
    congrArg Prod.snd haProfile
  have hbOut : outerMask m b.1.1 = outerMask m c.1 :=
    congrArg Prod.snd hbProfile
  have haX : canonicalMiddleTransfer ends m a.1.1 k zero ⊆
      middleMask m c.1 := by
    rw [← haMid]
    simpa only [middleMask] using hva.1
  have hbX : canonicalMiddleTransfer ends m b.1.1 k zero ⊆
      middleMask m c.1 := by
    rw [← hbMid]
    simpa only [middleMask] using hvb.1
  have haY : canonicalOuterTransfer ends m a.1.1 k zero ⊆
      outerMask m c.1 := by
    rw [← haOut]
    simpa only [outerMask] using hva.2.1
  have hbY : canonicalOuterTransfer ends m b.1.1 k zero ⊆
      outerMask m c.1 := by
    rw [← hbOut]
    simpa only [outerMask] using hvb.2.1
  have hX : X ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
    simpa only [X, canonicalMiddleTransferDifference, middleMask] using
      symmDiff_subset_of_subsets_ambient haX hbX
  have hY : Y ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
    simpa only [Y, canonicalOuterTransferDifference, outerMask] using
      symmDiff_subset_of_subsets_ambient haY hbY
  have hsrcX : sources ends X = ∅ := by
    dsimp only [X, canonicalMiddleTransferDifference]
    rw [sources_symmDiff, hva.2.2.1, hvb.2.2.1]
    exact symmDiff_self _
  have hsrcY : sources ends Y = ∅ := by
    dsimp only [Y, canonicalOuterTransferDifference]
    rw [sources_symmDiff, hva.2.2.2, hvb.2.2.2]
    exact symmDiff_self _
  refine ⟨d, leftSourcePattern_of_sourceless_balancedSwap
    c.2.1 hX hY hsrcX hsrcY, ?_⟩
  calc
    fourColorMaskProfile m d = fourColorMaskProfile m c.1 := by
      simp [d, canonicalQuadrangleCompletion,
        fourColorMaskProfile_balancedSwap]
    _ = p := c.2.2


noncomputable def canonicalQuadrangleCompletionSourceEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    leftSourceMaskFiber ends m j k l zero p ≃
      leftSourceMaskFiber ends m j k l zero p where
  toFun := canonicalQuadrangleCompletionSourceMap
    ends m j k l zero hloop hjk hkl p a b
  invFun := canonicalQuadrangleCompletionSourceMap
    ends m j k l zero hloop hjk hkl p a b
  left_inv := by
    intro c
    apply Subtype.ext
    exact canonicalQuadrangleCompletion_involutive
      ends m k zero a.1.1 b.1.1 c.1

  right_inv := by
    intro c
    apply Subtype.ext
    exact canonicalQuadrangleCompletion_involutive
      ends m k zero a.1.1 b.1.1 c.1


end StatMech.GrahamGHS.FourColor
