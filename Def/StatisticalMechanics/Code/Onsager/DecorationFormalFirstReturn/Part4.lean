/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part3


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFirstReturnAtomEquivSegment
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    ons_DecFirstReturnAtom L d ≃
      {segment : List (ons_Dart L) //
        ons_isFirstReturnSegment d segment ∧
          ∀ x ∈ segment, x ≠ ons_dartRev L d} :=
  Equiv.ofBijective
    (fun atom ↦ ⟨ons_decFirstReturnAtomSegment atom,
      ons_decFirstReturnAtomSegment_valid atom⟩)
    ⟨fun _ _ h ↦ ons_decFirstReturnAtomSegment_injective
      (congrArg Subtype.val h),
      ons_decFirstReturnAtomSegment_surjective⟩

end StatMech.Onsager
