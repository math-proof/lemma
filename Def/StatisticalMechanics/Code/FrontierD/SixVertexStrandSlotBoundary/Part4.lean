module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def fkColoredStrandSlotBoundaryPerm
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    Equiv.Perm (T.Vertex × Bool) :=
  (fkColoredBlackDartStrandSlotEquiv pairing).symm.trans
    ((fkMedialBlackBoundaryPerm pairing).trans
      (fkColoredBlackDartStrandSlotEquiv pairing))


end
end StatMech.FrontierD
