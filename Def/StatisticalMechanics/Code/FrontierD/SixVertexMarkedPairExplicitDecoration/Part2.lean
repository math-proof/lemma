/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexPreferredCompatiblePairing
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  if fkLoopPairingCompatible false omega v then false else true

end
end StatMech.FrontierD
