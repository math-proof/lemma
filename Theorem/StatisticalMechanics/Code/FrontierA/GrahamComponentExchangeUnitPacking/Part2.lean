/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking.Part4
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem card_componentExchangeSupportFiber_le_weight
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (R : rightRowSupportIndex ends m j k l zero) :
    Fintype.card (componentExchangeSupportFiber ends m j k l zero R) ≤
      rowSupportWeight ends m R.1 := by
  rw [← rightRowDataIndexFiber_card_eq_weight ends m j k l zero R]
  exact Fintype.card_le_of_injective
    (componentExchangeSupportFiberEmbedding ends m j k l zero
      hloop hjk hkl hk0 R)
    (componentExchangeSupportFiberEmbedding ends m j k l zero
      hloop hjk hkl hk0 R).injective


theorem leftRowData_card_eq_leftRowSupportIndex_of_unit_weight
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hunit : ∀ K ⊆ m, LeftRowSupport ends m j k l zero K →
      rowSupportWeight ends m K = 1) :
    Fintype.card (leftRowData ends m j k l zero) =
      Fintype.card (leftRowSupportIndex ends m j k l zero) := by
  classical
  rw [leftRowData_card_eq_weightedSum]
  calc
    (∑ K ∈ leftRowSupports ends m j k l zero,
        rowSupportWeight ends m K) =
        ∑ K ∈ leftRowSupports ends m j k l zero, 1 := by
      apply Finset.sum_congr rfl
      intro K hK
      have hK' : K ⊆ m ∧ LeftRowSupport ends m j k l zero K := by
        simpa [leftRowSupports] using hK
      exact hunit K hK'.1 hK'.2
    _ = (leftRowSupports ends m j k l zero).card := by simp
    _ = Fintype.card (leftRowSupportIndex ends m j k l zero) := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (fun K => by
        simp [leftRowSupports])


theorem GrahamWeightedRowMinor_of_unit_left_support_weights
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hunit : ∀ K ⊆ m, LeftRowSupport ends m j k l zero K →
      rowSupportWeight ends m K = 1) :
    GrahamWeightedRowMinor ends m j k l zero := by
  unfold GrahamWeightedRowMinor
  rw [← leftRowData_card_eq_weightedSum,
    leftRowData_card_eq_leftRowSupportIndex_of_unit_weight ends m j k l zero hunit,
    ← rightRowData_card_eq_weightedSum]
  exact card_leftRowSupportIndex_le_rightRowData
    ends m j k l zero hloop hjk hkl hk0

end StatMech.GrahamGHS.FourColor
