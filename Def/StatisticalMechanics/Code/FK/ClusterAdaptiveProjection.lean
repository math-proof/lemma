/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ClusterExplorationFreeBoundary
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def clusterAdaptiveInsideEdges (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) : Finset (Sym2 V) :=
  clusterUnexploredPairEdges G rho roots

end
end StatMech.FK
