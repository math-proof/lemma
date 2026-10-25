/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part5


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFirstReturnSegmentAtom_segment
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (segment : List (ons_Dart L))
    (hsegment : ons_isFirstReturnSegment d segment ∧
      ∀ x ∈ segment, x ≠ ons_dartRev L d) :
    ons_decFirstReturnAtomSegment
        (ons_decFirstReturnSegmentAtom L d segment) = segment := by
  unfold ons_decFirstReturnSegmentAtom
  rw [dif_pos hsegment]
  exact congrArg Subtype.val
    ((ons_decFirstReturnAtomEquivSegment L d).apply_symm_apply
      ⟨segment, hsegment⟩)

end StatMech.Onsager
