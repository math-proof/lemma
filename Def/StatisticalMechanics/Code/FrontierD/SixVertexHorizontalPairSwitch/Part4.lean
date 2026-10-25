/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalPairSwitchBoundaryBalanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    Prop :=
  (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
        (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) ≠
          mask v.1),
      sixVertexHorizontalPairBondCrossAgreementCount horizontal v) =
    ∑ v ∈ (Finset.univ : Finset T.Vertex).filter
        (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) ≠
          mask v.1),
      sixVertexHorizontalPairBondAgreementCount horizontal v

end
end StatMech.FrontierD
