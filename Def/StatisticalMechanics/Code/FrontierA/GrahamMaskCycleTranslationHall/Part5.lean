/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


noncomputable def cycleTranslateMinBadPair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p ×
      rightMaskFiber ends m j k l zero p := by
  let q := Classical.choice
    (rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c)
  exact Classical.choose
    ((Finset.univ : Finset
      (leftMaskFiber ends m j k l zero p ×
        rightMaskFiber ends m j k l zero p)).exists_min_image
      (cycleTranslateBadCount ends m j k l zero p)
      ⟨(c, q), Finset.mem_univ _⟩)


end StatMech.GrahamGHS.FourColor
