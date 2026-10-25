/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalPairSwitchRowBoundaryBalanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Prop :=
  forall j : Fin T.height,
    (∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) ≠ mask i),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j)) =
      ∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) ≠ mask i),
        sixVertexHorizontalPairBondAgreementCount horizontal (i, j)

end
end StatMech.FrontierD
