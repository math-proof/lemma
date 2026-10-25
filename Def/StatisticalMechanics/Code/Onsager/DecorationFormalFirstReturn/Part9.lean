/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part8


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decRootedAtomEquivRootedList
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    ons_DecRootedAtom L d ≃
      {w : List (ons_Dart L) //
        ons_validRootedList d (ons_dartRev L d) w ∧ 2 ≤ w.length} :=
  Equiv.ofBijective
    (fun atom ↦ ⟨ons_decRootedAtomList atom,
      ons_decRootedAtomList_valid L d atom⟩)
    ⟨fun _ _ h ↦ ons_decRootedAtomList_injective
      (congrArg Subtype.val h), by
        rintro ⟨w, hw, hlength⟩
        obtain ⟨atom, hatom⟩ :=
          ons_validRootedList_eq_closedFinLoop w hw hlength
        exact ⟨atom, Subtype.ext hatom⟩⟩

end StatMech.Onsager
