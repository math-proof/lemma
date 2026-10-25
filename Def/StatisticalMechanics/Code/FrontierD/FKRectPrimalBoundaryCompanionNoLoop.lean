/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryCompanionNoLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryCompanionUnique
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight


namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalRankOneRegularNeighborhood.ofCompanionUnique
    (R : FKRectTorus) (omega : R.Configuration)
    (hunique : ¬ FKRectHasNet R omega ->
      FKRectPrimalBoundaryCompanionUnique R omega)
    (hextreme : FKRectPrimalDevelopedExtremeSameSign R omega) :
    FKRectPrimalRankOneRegularNeighborhood R omega :=
  FKRectPrimalRankOneRegularNeighborhood.ofParts R omega
    (fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two
      R omega (fun hnoNet x =>
        card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_companionUnique
          R omega (hunique hnoNet) x))
    hextreme


end
end StatMech.FrontierD
