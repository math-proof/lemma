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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration


namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalDualCrossingSourceWitnessCore
    (R : FKRectTorus) (S : Finset (Fin (2 * R.height)))
    (eta : R.Configuration) : Prop :=
  S ⊆ fkRectPrimalDualCrossingRepresentativeSourceIndices R eta


def FKRectPrimalDualCrossingSourceWitness
    (R : FKRectTorus) (S : Finset (Fin (2 * R.height)))
    (eta : R.Configuration) : Prop :=
  FKRectCutClosedConfiguration R eta ∧
    FKRectPrimalDualCrossingSourceWitnessCore R S eta


def FKRectPrimalCrossingSourceWitnessCore
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : Prop :=
  S ⊆ fkRectRawHorizontalCrossingRepresentativeIndices R
    (fkRectForceCutClosed R eta)


def FKRectPrimalExploredVertex
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) (v : R.Vertex) : Prop :=
  ∃ i ∈ S,
    (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v


def fkRectTorusCutGraphEdges (R : FKRectTorus) :
    Finset (Sym2 R.Vertex) :=
  (fkRectTorusCutEdges R).image (fkRectTorusIndexedEdge R)

end
end StatMech.FrontierD
