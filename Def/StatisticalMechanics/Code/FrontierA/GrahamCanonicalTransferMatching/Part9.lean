/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part8
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskRightAugmentedMatchingPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S) : Finset
      (canonicalMaskRightAugmentedEquivType ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S) := by
  classical
  exact Finset.univ.filter fun ef =>
    CanonicalMaskRightAugmentedMatching
        ends m j k l zero p S c ef.1 ∧
      CanonicalMaskRightAugmentedMatching
        ends m j k l zero p S d ef.2

end StatMech.GrahamGHS.FourColor
