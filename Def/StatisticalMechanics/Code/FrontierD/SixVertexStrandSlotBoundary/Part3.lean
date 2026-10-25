/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part2


namespace StatMech.FrontierD

noncomputable section

def fkColoredVertexStrandSlotSwap
    {T : EvenTorus} (v : T.Vertex) :
    Equiv.Perm (T.Vertex × Bool) :=
  Equiv.swap (v, false) (v, true)

end
end StatMech.FrontierD
