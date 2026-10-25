/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3


namespace StatMech.FrontierD

noncomputable section

def fkColoredBlackDartStrandSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (dart : FKMedialBlackDart T) : T.Vertex × Bool :=
  (dart.1.1, fkColoredSideSlot (pairing dart.1.1) dart.1.2)

end
end StatMech.FrontierD
