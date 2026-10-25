/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskRightAugmentedMatching
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S) : Prop :=
  f c = none ∧
    ∀ x : ↑S, x ≠ c -> ∃ q,
      f x = some q ∧ q.1 ∈ canonicalMaskRightImages
        ends m j k l zero p x.1


noncomputable def canonicalMaskRightAugmentedAssignedImage
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (x : ↑S) (hxc : x ≠ c) :
    ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) :=
  (hf.2 x hxc).choose

end StatMech.GrahamGHS.FourColor
