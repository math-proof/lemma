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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part3


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectPrimalUnexploredEdges
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : Finset (Sym2 R.Vertex) := by
  classical
  exact (fkRectTorusGraph R).edgeFinset.filter fun e =>
    e ∉ fkRectTorusCutGraphEdges R ∧
      ¬ ∃ v w : R.Vertex, e = s(v, w) ∧
        (FKRectPrimalExploredVertex R S eta v ∨
          FKRectPrimalExploredVertex R S eta w)


noncomputable def fkRectPrimalUnexploredGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : SimpleGraph R.Vertex :=
  SimpleGraph.fromEdgeSet
    (fkRectPrimalUnexploredEdges R S eta : Set (Sym2 R.Vertex))


def FKRectPrimalUnexploredVertex
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :=
  {v : R.Vertex // ¬ FKRectPrimalExploredVertex R S eta v}

end
end StatMech.FrontierD
