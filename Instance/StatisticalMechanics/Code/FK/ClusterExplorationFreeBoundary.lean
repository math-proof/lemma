/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreEventLaw
import Def.StatisticalMechanics.Code.FK.ClusterExplorationFreeBoundary
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable instance instFintypeClusterUnexploredVertex
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) :
    Fintype (ClusterUnexploredVertex G rho roots) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instDecidableEqClusterUnexploredVertex
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) :
    DecidableEq (ClusterUnexploredVertex G rho roots) :=
  Classical.decEq _


end
end StatMech.FK
