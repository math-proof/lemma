/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part6
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FK

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]


theorem indexedBcProb_nonneg
    (ends : E -> Sym2 V) (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : E -> Bool) :
    0 <= indexedBcProb ends C p q omega :=
  div_nonneg (indexedBcWeight_pos ends C hp hp1 hq omega).le
    (indexedBcZ_pos ends C hp hp1 hq).le

theorem indexedBcProb_sum_eq_one
    (ends : E -> Sym2 V) (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ omega : E -> Bool, indexedBcProb ends C p q omega = 1 := by
  unfold indexedBcProb indexedBcZ
  rw [← Finset.sum_div]
  exact div_self (indexedBcZ_pos ends C hp hp1 hq).ne'

theorem indexedBcWeight_cross
    (ends : E -> Sym2 V)
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    (hCC' : C <= C') {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (a b : E -> Bool) :
    indexedBcWeight ends C p q a * indexedBcWeight ends C' p q b <=
      indexedBcWeight ends C p q (a ⊓ b) *
        indexedBcWeight ends C' p q (a ⊔ b) := by
  have hcluster :
      q ^ indexedNumClustersBC ends C a *
          q ^ indexedNumClustersBC ends C' b <=
        q ^ indexedNumClustersBC ends C (a ⊓ b) *
          q ^ indexedNumClustersBC ends C' (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq
      (indexedMixed_supermodular_bc ends C C' hCC' a b)
  have hedge := indexedEdgeProduct_logModular p a b
  have hedge0 : 0 <= indexedEdgeProduct p (a ⊓ b) *
      indexedEdgeProduct p (a ⊔ b) :=
    mul_nonneg (indexedEdgeProduct_pos hp hp1 _).le
      (indexedEdgeProduct_pos hp hp1 _).le
  unfold indexedBcWeight
  rw [show indexedEdgeProduct p a * q ^ indexedNumClustersBC ends C a *
        (indexedEdgeProduct p b * q ^ indexedNumClustersBC ends C' b) =
      (indexedEdgeProduct p a * indexedEdgeProduct p b) *
        (q ^ indexedNumClustersBC ends C a *
          q ^ indexedNumClustersBC ends C' b) by ring]
  rw [show indexedEdgeProduct p (a ⊓ b) *
        q ^ indexedNumClustersBC ends C (a ⊓ b) *
        (indexedEdgeProduct p (a ⊔ b) *
          q ^ indexedNumClustersBC ends C' (a ⊔ b)) =
      (indexedEdgeProduct p (a ⊓ b) * indexedEdgeProduct p (a ⊔ b)) *
        (q ^ indexedNumClustersBC ends C (a ⊓ b) *
          q ^ indexedNumClustersBC ends C' (a ⊔ b)) by ring]
  rw [hedge]
  exact mul_le_mul_of_nonneg_left hcluster hedge0

theorem indexedBcProb_cross
    (ends : E -> Sym2 V)
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    (hCC' : C <= C') {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (a b : E -> Bool) :
    indexedBcProb ends C p q a * indexedBcProb ends C' p q b <=
      indexedBcProb ends C p q (a ⊓ b) *
        indexedBcProb ends C' p q (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ : 0 < indexedBcZ ends C p q := indexedBcZ_pos ends C hp hp1 hq0
  have hZ' : 0 < indexedBcZ ends C' p q :=
    indexedBcZ_pos ends C' hp hp1 hq0
  unfold indexedBcProb
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ hZ')]
  exact indexedBcWeight_cross ends C C' hCC' hp hp1 hq a b

end
end StatMech.FK
