/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedExtremeClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryPotentialContradiction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part5
import Structure.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalRankOneRegularNeighborhood.ofParts
    (R : FKRectTorus) (omega : R.Configuration)
    (hunique : FKRectPrimalBoundaryFiberSameSignUnique R omega)
    (hextreme : FKRectPrimalDevelopedExtremeSameSign R omega) :
    FKRectPrimalRankOneRegularNeighborhood R omega where
  sameSign_unique := hunique
  developedExtreme_sameSign := hextreme


end
end StatMech.FrontierD
