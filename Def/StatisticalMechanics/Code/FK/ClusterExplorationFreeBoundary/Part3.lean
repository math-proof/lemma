/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreEventLaw
import Instance.StatisticalMechanics.Code.FK.ClusterExplorationFreeBoundary.Part2
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def clusterUnexploredPairEdges
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) : Finset (Sym2 V) :=
  ocd_innerEdgeFinset
    (Vin := ClusterUnexploredVertex G rho roots)
    (Subtype.val : ClusterUnexploredVertex G rho roots -> V)

def clusterNoBoundary (_ : V) : Prop := False

end
end StatMech.FK
