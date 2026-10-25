/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Def.StatisticalMechanics.Code.FK.MonoBC
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem numClustersBC_bot (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G (⊥ : SimpleGraph V) ω = numClusters G ω := by
  rw [numClustersBC, sup_bot_eq, numClusters, Nat.card_eq_fintype_card]

variable (bdry : V → Prop) [DecidablePred bdry]


theorem numClustersBC_boundaryClique (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G (StatMech.Lattice.boundaryCliqueGraph bdry) ω
      = StatMech.Lattice.numClustersWired G bdry ω := by
  rw [numClustersBC, StatMech.Lattice.numClustersWired, StatMech.Lattice.wiredGraph,
    openSub_eq_openGraph]


theorem mixed_supermodular_bc (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] (hCC' : C ≤ C') (a b : ConfigSpace (Sym2 V)) :
    numClustersBC G C a + numClustersBC G C' b
      ≤ numClustersBC G C (a ⊓ b) + numClustersBC G C' (a ⊔ b) := by
  classical
  
  have hinf : openSub G (a ⊓ b) = openSub G a ⊓ openSub G b := by
    ext i j; rw [SimpleGraph.inf_adj]; exact openSub_inf_adj G a b i j
  have hsup : openSub G (a ⊔ b) = openSub G a ⊔ openSub G b := by
    ext i j; rw [SimpleGraph.sup_adj]; exact openSub_sup_adj G a b i j
  
  rw [numClustersBC, numClustersBC, numClustersBC, numClustersBC, hinf, hsup]
  set A := openSub G a with hA
  set B := openSub G b with hB
  
  have hPQ : (A ⊓ B) ⊔ C ≤ A ⊔ C := sup_le_sup_right inf_le_left C
  have hmarg := card_connectedComponent_marginal hPQ (B ⊔ C')
  have hCC'' : C ⊔ C' = C' := sup_eq_right.mpr hCC'
  
  have hBAB : (A ⊓ B) ⊔ B = B := by rw [inf_comm, sup_comm, sup_inf_self]
  have e1 : (A ⊓ B) ⊔ C ⊔ (B ⊔ C') = B ⊔ C' := by
    calc (A ⊓ B) ⊔ C ⊔ (B ⊔ C')
        = ((A ⊓ B) ⊔ B) ⊔ (C ⊔ C') := by ac_rfl
      _ = B ⊔ C' := by rw [hBAB, hCC'']
  have e2 : A ⊔ C ⊔ (B ⊔ C') = A ⊔ B ⊔ C' := by
    calc A ⊔ C ⊔ (B ⊔ C')
        = (A ⊔ B) ⊔ (C ⊔ C') := by ac_rfl
      _ = A ⊔ B ⊔ C' := by rw [hCC'']
  rw [e1, e2] at hmarg
  
  omega


end FK
end StatMech
