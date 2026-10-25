/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part4
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileHall
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalProfileTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (left right : Fin (T.width + 1)) :=
  Sigma fun profile : SixVertexHorizontalPairCompletionProfile T =>
    Fin (sixVertexHorizontalPairProfileMultiplicity T grade profile *
      sixVertexHorizontalPairProfileChooseWeight left right profile)

end
end StatMech.FrontierD
