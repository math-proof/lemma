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
import Theorem.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def esMultiPoint (p : Real) (A : Finset V) : Real :=
  (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V -> Fin 2,
      esWeight G p sigma omega * esSpinProduct A sigma) / esZ G 2 p


noncomputable def allClustersEvenProb (p : Real) (A : Finset V) : Real :=
  ∑ omega ∈ Finset.univ.filter (fun omega : ConfigSpace (Sym2 V) =>
      AllClustersEven G omega A), fkProb G p 2 omega


end StatMech.FK
