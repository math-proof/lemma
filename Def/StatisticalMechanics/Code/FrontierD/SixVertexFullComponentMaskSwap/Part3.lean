/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexFullDisagreementVertexMask
    {T : EvenTorus} (mask : SixVertexArrows T) : T.Vertex -> Bool :=
  sixVertexTorusEdgeMaskVertexMask mask

end
end StatMech.FrontierD
