module
public import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
public import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
public import Def.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable instance instDecidableEqOpenConnectedComponent
    (omega : ConfigSpace (Sym2 V)) :
    DecidableEq (openSub G omega).ConnectedComponent :=
  Classical.decEq _

noncomputable instance instDecidableAllClustersEven (omega : ConfigSpace (Sym2 V))
    (A : Finset V) : Decidable (AllClustersEven G omega A) :=
  Classical.propDecidable _


end StatMech.FK
