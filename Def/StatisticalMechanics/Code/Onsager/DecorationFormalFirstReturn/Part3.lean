/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Abbrev.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn


namespace StatMech.Onsager

open BigOperators Finset

def ons_decFirstReturnAtomSegment
    {L : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtom L d) : List (ons_Dart L) :=
  List.ofFn atom.2.1 ++ [d]

end StatMech.Onsager
