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
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def fkRectCutConfigOfFull (R : FKRectTorus)
    (rho : ConfigSpace (Sym2 R.Vertex)) : FKRectCutClosedConfig R :=
  (fkRectCutClosedEdgeConfigEquiv R).symm
    (FK.ecz_closeOff (fkRectCutGraph R) rho)

end
end StatMech.FrontierD
