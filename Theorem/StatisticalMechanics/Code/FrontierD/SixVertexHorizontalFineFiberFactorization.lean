/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalPairBoundedFineRowProfile_eq_add
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBoundedFineRowProfile horizontal =
      sixVertexHorizontalAddSingleRowProfiles
        (sixVertexHorizontalBoundedSingleRowProfile horizontal.1)
        (sixVertexHorizontalBoundedSingleRowProfile horizontal.2) := by
  funext j
  apply Prod.ext <;> apply Fin.ext <;> rfl


end
end StatMech.FrontierD
