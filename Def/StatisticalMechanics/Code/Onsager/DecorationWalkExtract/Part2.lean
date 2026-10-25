/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycles
import Theorem.StatisticalMechanics.Code.Onsager.DecorationWalkExtract


namespace StatMech.Onsager

def ons_decCycleFirstReturn {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) : List (ons_Dart L) :=
  d :: (ons_decWalkExternalDarts q).tail.reverse ++ [d]

end StatMech.Onsager
