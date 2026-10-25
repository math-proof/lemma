/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part5


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFirstReturnAtomsSegments
    {L : ℕ} (d : ons_Dart L)
    (atoms : List (ons_DecFirstReturnAtom L d)) :
    List (List (ons_Dart L)) :=
  atoms.map ons_decFirstReturnAtomSegment

end StatMech.Onsager
