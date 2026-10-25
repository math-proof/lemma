/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskCommonReferenceEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference
      ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p :=
  canonicalOrbitSelectorMaskFiberEmbedding
    ends m j k l zero hloop hjk hkl p
    (canonicalMaskOrbitCommonReference ends m j k l zero p hcommon)
    (canonicalMaskOrbitCommonReference_selector
      ends m j k l zero p hcommon)
    (canonicalMaskOrbitCommonReference_works
      ends m j k l zero p hcommon)


end StatMech.GrahamGHS.FourColor
