/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLexComponentColoredSwap
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexLexDisagreementComponentVertexMask
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    T.Vertex -> Bool :=
  sixVertexTorusEdgeMaskVertexMask
    (sixVertexLexDisagreementComponentMask T omega eta h)

end
end StatMech.FrontierD
