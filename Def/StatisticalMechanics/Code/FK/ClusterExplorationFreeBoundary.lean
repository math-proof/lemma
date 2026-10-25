/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreEventLaw
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def ClusterExploredVertex (rho : ConfigSpace (Sym2 V))
    (roots : Finset V) (v : V) : Prop :=
  ∃ r ∈ roots, (openSub G rho).Reachable r v


def ClusterUnexploredVertex (rho : ConfigSpace (Sym2 V))
    (roots : Finset V) :=
  {v : V // ¬ ClusterExploredVertex G rho roots v}

end
end StatMech.FK
