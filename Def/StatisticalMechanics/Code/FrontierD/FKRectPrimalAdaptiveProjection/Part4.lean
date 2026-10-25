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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def fkRectPrimalAdaptiveInsideEdges
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Finset (Sym2 R.Vertex) :=
  fkRectPrimalFullUnexploredPairEdges R S rho


def fkRectPrimalAdaptiveProjection
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) : ConfigSpace (Sym2 R.Vertex) :=
  FK.projOff (fkRectPrimalAdaptiveInsideEdges R S rho) rho

end
end StatMech.FrontierD
