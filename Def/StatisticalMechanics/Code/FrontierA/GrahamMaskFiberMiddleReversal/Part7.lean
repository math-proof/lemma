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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def sourceMaskCycleDifference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftSourceMaskFiber ends m j k l zero p) :
    sourceMaskCycleSpace ends p := by
  let X := balancedMiddleDifference m c.1 d.1
  let Y := balancedOuterDifference m c.1 d.1
  have hprofile : fourColorMaskProfile m c.1 =
      fourColorMaskProfile m d.1 := c.2.2.trans d.2.2.symm
  have hmid : middleMask m c.1 = middleMask m d.1 :=
    congrArg Prod.fst hprofile
  have hout : outerMask m c.1 = outerMask m d.1 :=
    congrArg Prod.snd hprofile
  have hXsub : X ⊆ p.1 := by
    have h := balancedMiddleDifference_subset m c.1 d.1 hmid
    rw [show middleMask m c.1 = p.1 from congrArg Prod.fst c.2.2] at h
    exact h
  have hYsub : Y ⊆ p.2 := by
    have h := balancedOuterDifference_subset m c.1 d.1 hout
    rw [show outerMask m c.1 = p.2 from congrArg Prod.snd c.2.2] at h
    exact h
  have hXsrc : sources ends X = ∅ := by
    dsimp only [X]
    rw [balancedMiddleDifference, sources_symmDiff,
      c.2.1.2.1, d.2.1.2.1, symmDiff_self]
    simp
  have hYsrc : sources ends Y = ∅ := by
    dsimp only [Y]
    rw [balancedOuterDifference, sources_symmDiff,
      c.2.1.1, d.2.1.1, symmDiff_self]
    simp
  exact (⟨X, hXsub, hXsrc⟩, ⟨Y, hYsub, hYsrc⟩)

end StatMech.GrahamGHS.FourColor
