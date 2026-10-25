/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFlowConservation_of_ice
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : omega.IceRule) (v : T.Vertex) :
    ((omega.horizontal
          (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)).toNat : Int) +
        (omega.vertical
          (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)).toNat =
      (omega.horizontal v).toNat + (omega.vertical v).toNat := by
  have hice := homega v
  unfold SixVertexArrows.incomingCount at hice
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at hice ⊢
  generalize he : omega.horizontal v = e at hice ⊢
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at hice ⊢
  generalize hn : omega.vertical v = n at hice ⊢
  cases w <;> cases e <;> cases s <;> cases n
  all_goals norm_num at hice
  all_goals norm_num


theorem sixVertexPairUnion_isCirculation
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T)
    (hfirst : pair.1.IceRule) (hsecond : pair.2.IceRule) :
    SixVertexTorusCirculation T
      (sixVertexPairUnionHorizontal pair)
      (sixVertexPairUnionVertical pair) := by
  intro v
  have hfirstFlow := sixVertexFlowConservation_of_ice pair.1 hfirst v
  have hsecondFlow := sixVertexFlowConservation_of_ice pair.2 hsecond v
  unfold sixVertexPairUnionHorizontal sixVertexPairUnionVertical
  omega


end
end StatMech.FrontierD
