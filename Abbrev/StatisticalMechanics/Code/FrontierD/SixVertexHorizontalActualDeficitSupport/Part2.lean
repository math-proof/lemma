/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitSupport
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalActualDeficitTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :=
  Sigma fun profile : SixVertexHorizontalPairCompletionProfile T =>
    SixVertexHorizontalPairProfileFiber T grade profile ×
      Fin (sixVertexHorizontalProfileDeficit
        sourceLeft sourceRight targetLeft targetRight profile)

abbrev SixVertexHorizontalActualSurplusTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :=
  Sigma fun profile : SixVertexHorizontalPairCompletionProfile T =>
    SixVertexHorizontalPairProfileFiber T grade profile ×
      Fin (sixVertexHorizontalProfileSurplus
        sourceLeft sourceRight targetLeft targetRight profile)

end
end StatMech.FrontierD
