/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreEventLaw
import Def.StatisticalMechanics.Code.FK.ClusterExplorationFreeBoundary.Part2
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable instance instDecidableRelClusterUnexploredGraph
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) :
    DecidableRel (clusterUnexploredGraph G rho roots).Adj :=
  fun _ _ => Classical.dec _


end
end StatMech.FK
