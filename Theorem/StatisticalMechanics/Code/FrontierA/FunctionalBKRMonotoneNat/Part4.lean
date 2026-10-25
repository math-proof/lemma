/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part4
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem productExpectation_natAsReal_eq_levels (phi : E -> Bool -> ℝ)
    (F : ConfigSpace E -> ℕ) :
    productExpectation phi (natAsReal F) =
      ∑ k ∈ Finset.range (natFunctionBound F), wprob phi (natUpperLevel F k) := by
  unfold productExpectation wprob natAsReal
  have hlayer : ∀ omega : ConfigSpace E,
      (F omega : ℝ) =
        ∑ k ∈ Finset.range (natFunctionBound F),
          if k < F omega then (1 : ℝ) else 0 := by
    intro omega
    symm
    exact sum_range_indicator_eq (Nat.le_of_lt (lt_natFunctionBound F omega))
  simp_rw [hlayer, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hlevel : k < F omega <;>
    simp [natUpperLevel, Set.indicator, hlevel, mul_comm]


theorem functionalBKR_monotone_nat (phi : E -> Bool -> ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (F G : ConfigSpace E -> ℕ) (hF : Monotone F) (hG : Monotone G) :
    productExpectation phi (functionalDisjointMax (natAsReal F) (natAsReal G)) ≤
      productExpectation phi (natAsReal F) * productExpectation phi (natAsReal G) := by
  calc
    productExpectation phi (functionalDisjointMax (natAsReal F) (natAsReal G)) ≤
        ∑ omega : ConfigSpace E, pweight phi omega *
          (∑ k ∈ Finset.range (natFunctionBound F),
            ∑ l ∈ Finset.range (natFunctionBound G),
              eventIndicator
                (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) omega) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (functionalDisjointMax_natAsReal_le F G omega)
        (pweight_nonneg hphi0 omega)
    _ = ∑ k ∈ Finset.range (natFunctionBound F),
          ∑ l ∈ Finset.range (natFunctionBound G),
            wprob phi (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      unfold wprob eventIndicator
      apply Finset.sum_congr rfl
      intro omega homega
      rw [mul_comm]
    _ ≤ ∑ k ∈ Finset.range (natFunctionBound F),
          ∑ l ∈ Finset.range (natFunctionBound G),
            wprob phi (natUpperLevel F k) * wprob phi (natUpperLevel G l) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact bk_wprob_general phi hphi0 hphi1
        (natUpperLevel_isIncreasing hF k) (natUpperLevel_isIncreasing hG l)
    _ = productExpectation phi (natAsReal F) *
          productExpectation phi (natAsReal G) := by
      rw [productExpectation_natAsReal_eq_levels,
        productExpectation_natAsReal_eq_levels, Finset.sum_mul_sum]

end StatMech.FrontierA
