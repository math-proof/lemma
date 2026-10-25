/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Instance.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFirstReturnSegmentAtom
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (segment : List (ons_Dart L)) : ons_DecFirstReturnAtom L d := by
  classical
  exact if h : ons_isFirstReturnSegment d segment ∧
        ∀ x ∈ segment, x ≠ ons_dartRev L d then
      (ons_decFirstReturnAtomEquivSegment L d).symm ⟨segment, h⟩
    else default

end StatMech.Onsager
