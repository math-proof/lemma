/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskRightImages
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ r : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
        q.1.1 = balancedSwap m
          (canonicalMiddleTransfer ends m r.1.1 k zero)
          (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1

end StatMech.GrahamGHS.FourColor
