/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn


namespace StatMech.Onsager

open BigOperators Finset

section PathSum

variable {E M : Type*} [AddCommMonoid M]

def ons_pathSum (step : E → E → M) : List E → M
  | [] => 0
  | [_] => 0
  | x :: y :: tail => step x y + ons_pathSum step (y :: tail)

end PathSum
end StatMech.Onsager
