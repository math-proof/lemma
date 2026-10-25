/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathTwoChannelAdapter
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding.Part2
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

def fkRectStoppedPathFullRectangleEmbedding
    (R : FKRectTorus) (center : R.Vertex)
    (scale cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center (2 * scale) cut lower upper) :
    RlcConnectorVertex (scale : Int) -> R.Vertex :=
  fun z =>
    (fkRectLocalBoxEmbedding R center (2 * scale) cut lower upper hfit
      (rlcConnectorFullRectangleBoxInclusion scale z)).1

end
end StatMech.FrontierD
