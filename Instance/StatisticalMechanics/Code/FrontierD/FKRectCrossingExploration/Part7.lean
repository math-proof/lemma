/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
import Theorem.StatisticalMechanics.Code.Probability.FiniteWitnessUnionBound
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8


namespace StatMech.FrontierD

noncomputable section

noncomputable instance instDecidableRelPrimalExplorationInducedBoundary
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    DecidableRel (fkRectPrimalExplorationInducedBoundary R S eta).Adj :=
  fun _ _ => Classical.dec _


end
end StatMech.FrontierD
