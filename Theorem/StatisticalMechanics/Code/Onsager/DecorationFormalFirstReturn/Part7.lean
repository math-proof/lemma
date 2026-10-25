/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part7


namespace StatMech.Onsager

open BigOperators Finset

@[simp] theorem ons_decFirstReturnAtomsEquivFactorList_apply_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atoms : List (ons_DecFirstReturnAtom L d)) :
    (ons_decFirstReturnAtomsEquivFactorList L d atoms).1 =
      ons_decFirstReturnAtomsSegments d atoms := rfl

end StatMech.Onsager
