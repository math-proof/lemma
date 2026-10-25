/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskOrbitCommonReference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
    (c : leftMaskFiber ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose
    ((canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p c).exists_min_image
        (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
        (hcommon c))

end StatMech.GrahamGHS.FourColor
