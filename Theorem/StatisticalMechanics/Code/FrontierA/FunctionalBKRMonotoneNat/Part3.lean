/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem cylinderMin_natAsReal (F : ConfigSpace E -> ℕ) (K : Set E)
    (omega : ConfigSpace E) :
    cylinderMin (natAsReal F) K omega = cylinderMinNat F K omega := by
  unfold cylinderMin cylinderMinNat natAsReal
  symm
  exact Finset.comp_inf'_eq_inf'_comp (agreementFiber_nonempty K omega)
    (fun n : ℕ => (n : ℝ)) (fun x y => by simp)


theorem occursOn_natUpperLevel_iff (F : ConfigSpace E -> ℕ) (k : ℕ)
    (K : Set E) (omega : ConfigSpace E) :
    OccursOn (natUpperLevel F k) K omega ↔ k < cylinderMinNat F K omega := by
  unfold OccursOn natUpperLevel cylinderMinNat
  rw [Finset.lt_inf'_iff]
  constructor
  · intro h eta heta
    exact h eta (mem_agreementFiber.mp heta)
  · intro h eta hagree
    exact h eta (mem_agreementFiber.mpr hagree)


theorem cylinderMinNat_le_self (F : ConfigSpace E -> ℕ) (K : Set E)
    (omega : ConfigSpace E) : cylinderMinNat F K omega ≤ F omega := by
  unfold cylinderMinNat
  exact Finset.inf'_le _ (mem_agreementFiber.mpr (agreeOn_refl K omega))

theorem sum_range_indicator_eq {m M : ℕ} (hm : m ≤ M) :
    (∑ k ∈ Finset.range M, if k < m then (1 : ℝ) else 0) = m := by
  rw [Finset.sum_boole]
  have hfilter : (Finset.range M).filter (fun k => k < m) = Finset.range m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]


theorem cylinderMinNat_mul_le_levelBoxes (F G : ConfigSpace E -> ℕ)
    (K L : Set E) (hKL : Disjoint K L) (omega : ConfigSpace E) :
    (cylinderMinNat F K omega : ℝ) * cylinderMinNat G L omega ≤
      ∑ k ∈ Finset.range (natFunctionBound F),
        ∑ l ∈ Finset.range (natFunctionBound G),
          eventIndicator (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) omega := by
  let m := cylinderMinNat F K omega
  let n := cylinderMinNat G L omega
  have hm : m ≤ natFunctionBound F := by
    exact (cylinderMinNat_le_self F K omega).trans
      (Nat.le_of_lt (lt_natFunctionBound F omega))
  have hn : n ≤ natFunctionBound G := by
    exact (cylinderMinNat_le_self G L omega).trans
      (Nat.le_of_lt (lt_natFunctionBound G omega))
  have hmLayer := sum_range_indicator_eq (m := m) hm
  have hnLayer := sum_range_indicator_eq (m := n) hn
  rw [← hmLayer, ← hnLayer, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  by_cases hkm : k < m <;> by_cases hln : l < n
  · have hoccF : OccursOn (natUpperLevel F k) K omega :=
      (occursOn_natUpperLevel_iff F k K omega).mpr hkm
    have hoccG : OccursOn (natUpperLevel G l) L omega :=
      (occursOn_natUpperLevel_iff G l L omega).mpr hln
    have hbox : omega ∈ disjointOccurrence (natUpperLevel F k) (natUpperLevel G l) :=
      ⟨K, L, hKL, hoccF, hoccG⟩
    simp [eventIndicator, hkm, hln, hbox]
  · simp only [if_pos hkm, if_neg hln, mul_zero]
    unfold eventIndicator
    exact Set.indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) _
  · simp only [if_neg hkm, zero_mul]
    unfold eventIndicator
    exact Set.indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) _
  · simp only [if_neg hkm, zero_mul]
    unfold eventIndicator
    exact Set.indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) _


theorem functionalDisjointMax_natAsReal_le (F G : ConfigSpace E -> ℕ)
    (omega : ConfigSpace E) :
    functionalDisjointMax (natAsReal F) (natAsReal G) omega ≤
      ∑ k ∈ Finset.range (natFunctionBound F),
        ∑ l ∈ Finset.range (natFunctionBound G),
          eventIndicator (disjointOccurrence (natUpperLevel F k) (natUpperLevel G l)) omega := by
  unfold functionalDisjointMax functionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  rw [cylinderMin_natAsReal, cylinderMin_natAsReal]
  exact cylinderMinNat_mul_le_levelBoxes F G pair.1 pair.2
    (mem_disjointCoordinatePairs.mp hpair) omega


end StatMech.FrontierA
