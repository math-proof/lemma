/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part2
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FK

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]


theorem indexedEdgeProduct_pos {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (omega : E -> Bool) :
    0 < indexedEdgeProduct p omega := by
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith

theorem indexedEdgeProduct_logModular
    (p : Real) (a b : E -> Bool) :
    indexedEdgeProduct p a * indexedEdgeProduct p b =
      indexedEdgeProduct p (a ⊓ b) * indexedEdgeProduct p (a ⊔ b) := by
  unfold indexedEdgeProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rw [Pi.inf_apply, Pi.sup_apply]
  cases a e <;> cases b e <;> simp
  all_goals ring


theorem card_connectedComponent_antitone
    {G H : SimpleGraph V} (hGH : G <= H) :
    Nat.card H.ConnectedComponent <= Nat.card G.ConnectedComponent := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  have h := card_connectedComponent_marginal hGH H
  rw [sup_eq_right.mpr hGH, sup_idem] at h
  omega


end
end StatMech.FK
