/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part7
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskOrbitMinimumReference_disconnects
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hdescent : CanonicalMaskOrbitLocalDescent ends m j k l zero p)
    (d : leftMaskFiber ends m j k l zero p) :
    RowsDisconnect ends m
      (balancedSwap m
        (canonicalMiddleTransfer ends m
          (canonicalMaskOrbitMinimumReference
            ends m j k l zero p d).1.1 k zero)
        (canonicalOuterTransfer ends m
          (canonicalMaskOrbitMinimumReference
            ends m j k l zero p d).1.1 k zero)
        d.1.1) k zero := by
  by_contra hbad
  let r := canonicalMaskOrbitMinimumReference ends m j k l zero p d
  have hdr : CanonicalMaskTransferOrbit ends m j k l zero p d r :=
    canonicalMaskOrbitMinimumReference_mem ends m j k l zero p d
  have hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d :=
    canonicalMaskTransferOrbit_symm ends m j k l zero p hdr
  have hlt : canonicalTransferSize ends m k zero d.1.1 <
      canonicalTransferSize ends m k zero r.1.1 :=
    hdescent r d hrd (by simpa only [r] using hbad)
  have hle : canonicalTransferSize ends m k zero r.1.1 ≤
      canonicalTransferSize ends m k zero d.1.1 := by
    simpa only [r] using canonicalMaskOrbitMinimumReference_size_le
      ends m j k l zero p d d
        (canonicalMaskTransferOrbit_refl ends m j k l zero p d)
  exact (not_lt_of_ge hle) hlt


end StatMech.GrahamGHS.FourColor
