/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
open Finset


namespace StatMech.Universality

noncomputable section

theorem isingCenteredPrimitive_horizontal_increment
    (horizontal vertical : Nat → Nat → Real)
    (center i j : Nat) :
    isingCenteredPrimitive horizontal vertical center (i + 1) j -
        isingCenteredPrimitive horizontal vertical center i j = horizontal i j := by
  unfold isingCenteredPrimitive
  have hs := isingCenteredSum_succ_sub
    (fun k ↦ horizontal k j) center i
  linarith

theorem isingCenteredSum_row_difference
    (horizontal vertical : Nat → Nat → Real)
    (center i j : Nat)
    (hclosed : ∀ k, (center ≤ k ∧ k < i) ∨ (i ≤ k ∧ k < center) →
      vertical k j + horizontal k (j + 1) =
        horizontal k j + vertical (k + 1) j) :
    isingCenteredSum (fun k ↦ horizontal k (j + 1)) center i -
        isingCenteredSum (fun k ↦ horizontal k j) center i =
      vertical i j - vertical center j := by
  by_cases hci : center ≤ i
  · rw [isingCenteredSum, if_pos hci, isingCenteredSum, if_pos hci,
      ← Finset.sum_sub_distrib]
    calc
      (∑ k ∈ Ico center i, (horizontal k (j + 1) - horizontal k j)) =
          ∑ k ∈ Ico center i, (vertical (k + 1) j - vertical k j) := by
        apply sum_congr rfl
        intro k hk
        have hb := (mem_Ico.mp hk)
        have hc := hclosed k (Or.inl hb)
        linarith
      _ = vertical i j - vertical center j := by
        exact sum_Ico_sub (fun k : Nat ↦ vertical k j) hci
  · have hic : i ≤ center := by omega
    rw [isingCenteredSum, if_neg hci, isingCenteredSum, if_neg hci,
      neg_sub_neg, ← Finset.sum_sub_distrib]
    calc
      (∑ k ∈ Ico i center, (horizontal k j - horizontal k (j + 1))) =
          ∑ k ∈ Ico i center, (vertical k j - vertical (k + 1) j) := by
        apply sum_congr rfl
        intro k hk
        have hb := (mem_Ico.mp hk)
        have hc := hclosed k (Or.inr hb)
        linarith
      _ = -(∑ k ∈ Ico i center,
          (vertical (k + 1) j - vertical k j)) := by
        rw [← Finset.sum_neg_distrib]
        apply sum_congr rfl
        intro k _
        ring
      _ = vertical i j - vertical center j := by
        rw [sum_Ico_sub (fun k : Nat ↦ vertical k j) hic]
        ring

theorem isingCenteredPrimitive_vertical_increment
    (horizontal vertical : Nat → Nat → Real)
    (center i j : Nat)
    (hclosed : ∀ k, (center ≤ k ∧ k < i) ∨ (i ≤ k ∧ k < center) →
      vertical k j + horizontal k (j + 1) =
        horizontal k j + vertical (k + 1) j) :
    isingCenteredPrimitive horizontal vertical center i (j + 1) -
        isingCenteredPrimitive horizontal vertical center i j = vertical i j := by
  have hv := isingCenteredSum_succ_sub
    (fun k ↦ vertical center k) center j
  have hh := isingCenteredSum_row_difference
    horizontal vertical center i j hclosed
  unfold isingCenteredPrimitive
  linarith

end
end StatMech.Universality
