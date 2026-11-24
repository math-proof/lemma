module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanBaseCases.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part35
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching
open Filter Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

abbrev OddPrismTransferSkewSwitchingPairing
    (beta : Real) (n : Nat) (r : Real) :=
  FiniteExpVarianceSkewSwitchingPairing
    (oddPrismTransferPairBaseWeight beta n)
    (oddPrismTransferPairInteraction n) r


end
end StatMech.FrontierA
