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
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

structure FKRectPrimalRankOneRegularNeighborhood
    (R : FKRectTorus) (omega : R.Configuration) : Prop where
  sameSign_unique : FKRectPrimalBoundaryFiberSameSignUnique R omega
  developedExtreme_sameSign : FKRectPrimalDevelopedExtremeSameSign R omega


end
end StatMech.FrontierD
