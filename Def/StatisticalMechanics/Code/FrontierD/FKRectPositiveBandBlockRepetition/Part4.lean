/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part3
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectColumnBandGridEquiv
    (R : FKRectTorus) (right lower upper : Nat)
    (hright : right < R.width) (hlowerUpper : lower ≤ upper)
    (hupper : upper < R.height) :
    (Fin right × Fin (upper + 1 - lower)) ≃
      FKRectColumnBandVertex R 1 right lower upper where
  toFun z := ⟨
    (⟨z.1.val + 1, by omega⟩, ⟨lower + z.2.val, by
      have hz := z.2.isLt
      omega⟩), by
        change 1 ≤ z.1.val + 1 ∧ z.1.val + 1 ≤ right ∧
          lower ≤ lower + z.2.val ∧ lower + z.2.val ≤ upper
        have hz := z.2.isLt
        omega⟩
  invFun v :=
    (⟨v.1.1.val - 1, by
      have hv := v.2
      change 1 ≤ v.1.1.val ∧ v.1.1.val ≤ right ∧
        lower ≤ v.1.2.val ∧ v.1.2.val ≤ upper at hv
      omega⟩,
     ⟨v.1.2.val - lower, by
      have hv := v.2
      change 1 ≤ v.1.1.val ∧ v.1.1.val ≤ right ∧
        lower ≤ v.1.2.val ∧ v.1.2.val ≤ upper at hv
      omega⟩)
  left_inv z := by
    apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · have hv := v.2
      change 1 ≤ v.1.1.val ∧ v.1.1.val ≤ right ∧
        lower ≤ v.1.2.val ∧ v.1.2.val ≤ upper at hv
      change v.1.1.val - 1 + 1 = v.1.1.val
      omega
    · have hv := v.2
      change 1 ≤ v.1.1.val ∧ v.1.1.val ≤ right ∧
        lower ≤ v.1.2.val ∧ v.1.2.val ≤ upper at hv
      change lower + (v.1.2.val - lower) = v.1.2.val
      omega


end
end StatMech.FrontierD
