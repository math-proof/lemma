module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
public import Theorem.StatisticalMechanics.Code.Probability.FiniteWitnessUnionBound
public import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
public import Def.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable instance instDecidableRelPrimalExplorationOutsideOpenGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    DecidableRel (fkRectPrimalExplorationOutsideOpenGraph R S eta).Adj :=
  fun _ _ => Classical.dec _


end
end StatMech.FrontierD
