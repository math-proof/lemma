/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalPairBondAgreementCount
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (v : T.Vertex) : Nat :=
  boolPairAgreementCount
    (sixVertexHorizontalGaugeBit horizontal.1
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2))
    (sixVertexHorizontalGaugeBit horizontal.2
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2))
    (sixVertexHorizontalGaugeBit horizontal.1 v)
    (sixVertexHorizontalGaugeBit horizontal.2 v)

def sixVertexHorizontalPairBondCrossAgreementCount
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (v : T.Vertex) : Nat :=
  boolPairCrossAgreementCount
    (sixVertexHorizontalGaugeBit horizontal.1
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2))
    (sixVertexHorizontalGaugeBit horizontal.2
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2))
    (sixVertexHorizontalGaugeBit horizontal.1 v)
    (sixVertexHorizontalGaugeBit horizontal.2 v)

end
end StatMech.FrontierD
