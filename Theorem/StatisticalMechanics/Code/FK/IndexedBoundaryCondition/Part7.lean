/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FK

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]


theorem indexedBcEventMass_mono_bc
    (ends : E -> Sym2 V)
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    (hCC' : C <= C') {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A : Set (E -> Bool)} (hA : IsIncreasing A) :
    indexedBcEventMass ends C p q A <=
      indexedBcEventMass ends C' p q A := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  unfold indexedBcEventMass
  apply holley_dominates
  · exact indexedBcProb_nonneg ends C hp hp1 hq0
  · exact indexedBcProb_nonneg ends C' hp hp1 hq0
  · rw [indexedBcProb_sum_eq_one ends C hp hp1 hq0,
      indexedBcProb_sum_eq_one ends C' hp hp1 hq0]
  · exact indexedBcProb_cross ends C C' hCC' hp hp1 hq
  · exact hA

end
end StatMech.FK
