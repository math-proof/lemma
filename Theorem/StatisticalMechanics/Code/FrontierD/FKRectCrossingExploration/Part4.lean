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
import Instance.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalUnexploredInducedGraph_adjMatch
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FK.ocd_AdjMatch
      (fkRectPrimalUnexploredInducedGraph R S eta)
      (fkRectCutGraph R)
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) := by
  intro x y
  rfl


end
end StatMech.FrontierD
