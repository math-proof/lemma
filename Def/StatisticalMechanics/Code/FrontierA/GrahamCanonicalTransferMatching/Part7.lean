/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part6
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskRightAugmentedAssignedRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact (T.erase c.1).attach.image fun x =>
    (canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf
      ⟨x.1, hTS (Finset.mem_of_mem_erase x.2)⟩ (by
        intro h
        exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h))).1

end StatMech.GrahamGHS.FourColor
