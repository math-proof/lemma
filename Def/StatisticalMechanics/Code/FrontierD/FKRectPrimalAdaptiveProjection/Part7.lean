/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalWitnessStep.Part2
import Theorem.StatisticalMechanics.Code.Probability.AdaptiveFibreStep
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part7
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def FKRectPrimalStableCrossingWitnessCore
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : Prop :=
  FKRectPrimalFullDistinctCrossingWitness R S
    (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))

end
end StatMech.FrontierD
