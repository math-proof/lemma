module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
public import Theorem.StatisticalMechanics.Code.Probability.FiniteWitnessUnionBound
public import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
public import Instance.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration


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

theorem fkRectCriticalEventMass_eq_finiteEventMass
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      StatMech.Probability.finiteEventMass
        (fun eta => fkRectCriticalRandomClusterProb R q eta) A := by
  classical
  unfold fkRectCriticalEventMass StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro eta heta
  by_cases hA : eta ∈ A <;> simp [Set.indicator, hA]


end
end StatMech.FrontierD
