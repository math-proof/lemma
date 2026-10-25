/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusAngularSplit
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5


namespace StatMech.FrontierA

open SimpleGraph


def triangularTorusDirectionRank : Fin 6 -> Fin 6 :=
  ![5, 2, 1, 4, 0, 3]


def triangularTorusDirectionRankEquiv : Equiv.Perm (Fin 6) where
  toFun := triangularTorusDirectionRank
  invFun := ![4, 2, 1, 5, 3, 0]
  left_inv a := by
    fin_cases a <;> rfl
  right_inv a := by
    fin_cases a <;> rfl


noncomputable def triangularTorusOutgoingDirectionEquiv
    (L : Nat) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    KWOutgoingDart (G := triangularTorusGraph L) v ≃ Fin 6 where
  toFun d := triangularTorusGraphDartDirection L d.1
  invFun a := ⟨triangularTorusDartEquiv L (v, a), rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply (triangularTorusDartEquiv L).symm.injective
    rw [Equiv.symm_apply_apply]
    apply Prod.ext
    · have h := congrArg (fun z : (triangularTorusGraph L).Dart => z.fst)
        ((triangularTorusDartEquiv L).apply_symm_apply d.1)
      exact (h.trans d.2).symm
    · rfl
  right_inv a := by
    change ((triangularTorusDartEquiv L).symm
      (triangularTorusDartEquiv L (v, a))).2 = a
    rw [Equiv.symm_apply_apply]

end StatMech.FrontierA
