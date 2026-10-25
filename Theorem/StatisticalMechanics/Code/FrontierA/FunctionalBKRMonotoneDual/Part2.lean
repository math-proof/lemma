/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneReal.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterfly
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneDual
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem dualWprob_mono {phi : E → Bool → ℝ} (hphi0 : ∀ e b, 0 ≤ phi e b)
    {C D : Set (ConfigSpace E × ConfigSpace E)} (hCD : C ⊆ D) :
    dualWprob phi C ≤ dualWprob phi D := by
  unfold dualWprob
  apply Finset.sum_le_sum
  intro omega _
  apply Finset.sum_le_sum
  intro eta _
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
  by_cases hC : (omega, eta) ∈ C
  · rw [Set.indicator_of_mem hC, Set.indicator_of_mem (hCD hC)]
  · rw [Set.indicator_of_notMem hC]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _


theorem dualWprob_prod (phi : E → Bool → ℝ)
    (A B : Set (ConfigSpace E)) :
    dualWprob phi (A ×ˢ B) = wprob phi A * wprob phi B := by
  unfold dualWprob wprob
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  apply Finset.sum_congr rfl
  intro eta _
  by_cases hA : omega ∈ A <;> by_cases hB : eta ∈ B <;>
    simp [Set.indicator, hA, hB]

omit [Fintype E] [DecidableEq E] in


theorem dualDisjointOccurrence_subset_prod (A B : Set (ConfigSpace E)) :
    dualDisjointOccurrence A B ⊆ A ×ˢ B := by
  rintro ⟨omega, eta⟩ ⟨K, L, hKL, hA, hB⟩
  exact ⟨hA omega (agreeOn_refl K omega),
    hB eta (agreeOn_refl L eta)⟩


theorem dualBKR_wprob_increasing (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
  calc
    dualWprob phi (dualDisjointOccurrence A B) ≤
        dualWprob phi (A ×ˢ B) :=
      dualWprob_mono hphi0 (dualDisjointOccurrence_subset_prod A B)
    _ = wprob phi A * wprob phi B := dualWprob_prod phi A B
    _ ≤ wprob phi (A ∩ B) := wprob_fkg_pos phi hphi0 hphi1 hA hB

theorem dual_sum_range_indicator_eq {m M : ℕ} (hm : m ≤ M) :
    (∑ k ∈ Finset.range M, if k < m then (1 : ℝ) else 0) = m := by
  rw [Finset.sum_boole]
  have hfilter : (Finset.range M).filter (fun k => k < m) = Finset.range m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]


end StatMech.FrontierA
