/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part3
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FK

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]


theorem indexedMixed_supermodular_bc
    (ends : E -> Sym2 V)
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    (hCC' : C <= C') (a b : E -> Bool) :
    indexedNumClustersBC ends C a + indexedNumClustersBC ends C' b <=
      indexedNumClustersBC ends C (a ⊓ b) +
        indexedNumClustersBC ends C' (a ⊔ b) := by
  classical
  let A := indexedOpenGraph ends a
  let B := indexedOpenGraph ends b
  let I := indexedOpenGraph ends (a ⊓ b)
  let U := indexedOpenGraph ends (a ⊔ b)
  have hI : I <= A ⊓ B := indexedOpenGraph_inf_le ends a b
  have hU : U = A ⊔ B := indexedOpenGraph_sup ends a b
  have hPQ : (A ⊓ B) ⊔ C <= A ⊔ C :=
    sup_le_sup_right inf_le_left C
  have hmarg := card_connectedComponent_marginal hPQ (B ⊔ C')
  have hCC'' : C ⊔ C' = C' := sup_eq_right.mpr hCC'
  have hBAB : (A ⊓ B) ⊔ B = B := by
    rw [inf_comm, sup_comm, sup_inf_self]
  have e1 : (A ⊓ B) ⊔ C ⊔ (B ⊔ C') = B ⊔ C' := by
    calc
      (A ⊓ B) ⊔ C ⊔ (B ⊔ C') =
          ((A ⊓ B) ⊔ B) ⊔ (C ⊔ C') := by ac_rfl
      _ = B ⊔ C' := by rw [hBAB, hCC'']
  have e2 : A ⊔ C ⊔ (B ⊔ C') = A ⊔ B ⊔ C' := by
    calc
      A ⊔ C ⊔ (B ⊔ C') = (A ⊔ B) ⊔ (C ⊔ C') := by ac_rfl
      _ = A ⊔ B ⊔ C' := by rw [hCC'']
  rw [e1, e2] at hmarg
  have hmeet : Nat.card ((A ⊓ B) ⊔ C).ConnectedComponent <=
      Nat.card (I ⊔ C).ConnectedComponent :=
    card_connectedComponent_antitone (sup_le_sup_right hI C)
  unfold indexedNumClustersBC
  change Nat.card (A ⊔ C).ConnectedComponent +
      Nat.card (B ⊔ C').ConnectedComponent <=
    Nat.card (I ⊔ C).ConnectedComponent +
      Nat.card (U ⊔ C').ConnectedComponent
  rw [hU]
  omega

end
end StatMech.FK
