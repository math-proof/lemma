/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLexComponentColoredSwap.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexLexDisagreementComponentColoredTarget
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty) :
    FKColoredLoopPairingPair T :=
  fkColoredFullSwapTarget source
    (sixVertexLexDisagreementComponentVertexMask T
      (source false).arrows (source true).arrows h)
    (sixVertexLexDisagreementComponent_fullSwapBondCoherent source h)

end
end StatMech.FrontierD
