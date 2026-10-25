/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part8
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalMaskOrbitCommonReferenceFinset_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c r : leftMaskFiber ends m j k l zero p) :
    r ∈ canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c ↔
      CanonicalMaskTransferOrbit ends m j k l zero p c r ∧
        ∀ d, CanonicalMaskTransferOrbit ends m j k l zero p c d ->
          CanonicalTransferWorks ends m k zero r.1.1 d.1.1 := by
  classical
  simp [canonicalMaskOrbitCommonReferenceFinset]


end StatMech.GrahamGHS.FourColor
