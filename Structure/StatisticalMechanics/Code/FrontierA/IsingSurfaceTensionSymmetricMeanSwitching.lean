/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanBaseCases.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part35
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

structure FiniteExpVarianceSkewSwitchingPairing
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real) where
  switch : (E × E × E × E) ≃ (E × E × E × E)
  pair_nonpos : forall s,
    finiteExpVarianceSkewFourSummand w I r s +
      finiteExpVarianceSkewFourSummand w I r (switch s) <= 0


end
end StatMech.FrontierA
