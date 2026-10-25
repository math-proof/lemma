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
import Def.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part5


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalExploration_cutGraph_condFkProb_eq_induced
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta omega : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.condFkProb (fkRectCutGraph R) p q
        (fkRectPrimalUnexploredPairEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (fkRectFullGraphConfiguration R omega) =
      FK.inducedFkProb (fkRectCutGraph R) p q
        (fkRectPrimalUnexploredPairEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (fkRectFullGraphConfiguration R omega) := by
  exact FK.condFkProb_eq_inducedFkProb
    (fkRectCutGraph R) hp hp1 hq _ _ _

end
end StatMech.FrontierD
