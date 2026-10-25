/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem rby_card_mul_four_fiber (𝒜 ℬ : Finset (Finset α)) (i : α) :
    𝒜.card * ℬ.card
      = (𝒜.nonMemberSubfamily i).card * (ℬ.nonMemberSubfamily i).card
      + (𝒜.memberSubfamily i).card * (ℬ.nonMemberSubfamily i).card
      + (𝒜.nonMemberSubfamily i).card * (ℬ.memberSubfamily i).card
      + (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card := by
  have hA := card_family_fiber_split 𝒜 i
  have hB := card_family_fiber_split ℬ i
  nlinarith [hA, hB]


theorem rby_dpairsCount_add_member_le_mul (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ
        + (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card
      ≤ 𝒜.card * ℬ.card := by
  have hrec := dpairsCount_fiber_recursion 𝒜 ℬ i
  have h1 := dpairsCount_le_mul (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
  have h2 := dpairsCount_le_mul (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
  have h3 := dpairsCount_le_mul (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)
  rw [hrec, rby_card_mul_four_fiber 𝒜 ℬ i]
  nlinarith [h1, h2, h3]


theorem rby_mul_sub_dpairsCount_ge_member (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card
      ≤ 𝒜.card * ℬ.card - dpairsCount 𝒜 ℬ := by
  have h := rby_dpairsCount_add_member_le_mul 𝒜 ℬ i
  omega


end StatMech
