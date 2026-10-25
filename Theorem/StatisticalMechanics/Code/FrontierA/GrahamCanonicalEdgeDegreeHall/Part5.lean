/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightPreimageReference_works
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q : rightMaskFiber ends m j k l zero p)
    (d : {d : leftMaskFiber ends m j k l zero p //
      q ∈ canonicalMaskRightImages ends m j k l zero p d}) :
    CanonicalTransferWorks ends m k zero
      (canonicalMaskRightPreimageReference
        ends m j k l zero p q d).1.1 d.1.1.1 :=
  (Classical.choose_spec ((mem_canonicalMaskRightImages_iff
    ends m j k l zero p d.1 q).mp d.2)).1

theorem canonicalMaskRightPreimageReference_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q : rightMaskFiber ends m j k l zero p)
    (d : {d : leftMaskFiber ends m j k l zero p //
      q ∈ canonicalMaskRightImages ends m j k l zero p d}) :
    q.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m
        (canonicalMaskRightPreimageReference
          ends m j k l zero p q d).1.1 k zero)
      (canonicalOuterTransfer ends m
        (canonicalMaskRightPreimageReference
          ends m j k l zero p q d).1.1 k zero) d.1.1.1 :=
  (Classical.choose_spec ((mem_canonicalMaskRightImages_iff
    ends m j k l zero p d.1 q).mp d.2)).2


end StatMech.GrahamGHS.FourColor
