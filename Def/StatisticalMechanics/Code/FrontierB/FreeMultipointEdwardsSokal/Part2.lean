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
import Instance.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


def esSpinProduct (A : Finset V) (sigma : V -> Fin 2) : Real :=
  ∏ x ∈ A, isingSpin (sigma x)

end StatMech.FK
