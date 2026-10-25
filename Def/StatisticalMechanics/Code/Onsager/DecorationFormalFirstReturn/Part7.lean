/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part6


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFirstReturnAtomsEquivFactorList
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    List (ons_DecFirstReturnAtom L d) ≃
      {segments : List (List (ons_Dart L)) //
        ons_validFactorList d (ons_dartRev L d) segments} :=
  Equiv.ofBijective
    (fun atoms ↦ ⟨ons_decFirstReturnAtomsSegments d atoms,
      ons_decFirstReturnAtomsSegments_valid L d atoms⟩)
    ⟨fun _ _ h ↦ ons_decFirstReturnAtomsSegments_injective
      (congrArg Subtype.val h), by
        rintro ⟨segments, hsegments⟩
        obtain ⟨atoms, hatoms⟩ :=
          ons_decFirstReturnAtomsSegments_surjective_valid
            L d segments hsegments
        exact ⟨atoms, Subtype.ext hatoms⟩⟩

end StatMech.Onsager
