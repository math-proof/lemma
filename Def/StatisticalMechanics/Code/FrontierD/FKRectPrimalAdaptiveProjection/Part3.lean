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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def fkRectPrimalFullUnexploredPairEdges
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Finset (Sym2 R.Vertex) := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ x y : R.Vertex, e = s(x, y) ∧
      ¬ FKRectPrimalFullExploredVertex R S rho x ∧
      ¬ FKRectPrimalFullExploredVertex R S rho y

end
end StatMech.FrontierD
