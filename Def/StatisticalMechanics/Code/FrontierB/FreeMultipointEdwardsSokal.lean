/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def clusterMarkCount (omega : ConfigSpace (Sym2 V)) (A : Finset V)
    (C : (openSub G omega).ConnectedComponent) : Nat := by
  classical
  exact (A.filter fun x => (openSub G omega).connectedComponentMk x = C).card


def AllClustersEven (omega : ConfigSpace (Sym2 V)) (A : Finset V) : Prop :=
  ∀ C : (openSub G omega).ConnectedComponent, Even (clusterMarkCount G omega A C)

end StatMech.FK
