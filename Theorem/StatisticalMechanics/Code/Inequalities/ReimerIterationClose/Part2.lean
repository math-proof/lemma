/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Inequalities.ReimerIterationClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rit_wHalf_prob : ∀ x, rit_wHalf x false + rit_wHalf x true = 1 := by
  intro x; norm_num [rit_wHalf]

theorem rit_wHalf_nonneg : ∀ x b, 0 ≤ rit_wHalf x b := by
  intro x b; norm_num [rit_wHalf]


theorem rit_collapseLHS :
    wprob rit_wHalf (disjointOccurrence
        (familyEvent (Finset.univ.powerset : Finset (Finset (Fin 1))))
        (familyEvent (Finset.univ.powerset))) = 1 := by
  rw [rit_familyEvent_powerset_univ, rit_disjointOccurrence_univ_univ]
  simp only [wprob, Set.indicator_univ, one_mul]
  exact sum_pweight_eq_one rit_wHalf_prob


theorem rit_collapseRHS :
    wdpairs rit_wHalf (Finset.univ.powerset : Finset (Finset (Fin 1)))
        (Finset.univ.powerset) = 3 / 4 := by
  unfold wdpairs
  have hfwt : ∀ S : Finset (Fin 1), fwt rit_wHalf S = 1 / 2 := by
    intro S; simp only [fwt, rit_wHalf]; rw [Finset.prod_const]; simp
  rw [Finset.sum_congr rfl (fun p _ => by rw [hfwt p.1, hfwt p.2])]
  rw [Finset.sum_const]
  have hcard : ((Finset.univ.powerset ×ˢ Finset.univ.powerset :
        Finset (Finset (Fin 1) × Finset (Fin 1))).filter
        (fun p => Disjoint p.1 p.2)).card = 3 := by decide
  rw [hcard]; norm_num


theorem rit_collapseDomination_false :
    ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β) (w : β → Bool → ℝ),
      (∀ x b, 0 ≤ w x b) ∧ (∀ x, w x false + w x true = 1) ∧ (∀ x, w x false = w x true) ∧
      ∃ 𝒜 ℬ : Finset (Finset β),
        wdpairs w 𝒜 ℬ
          < wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) := by
  refine ⟨Fin 1, inferInstance, inferInstance, rit_wHalf, rit_wHalf_nonneg, rit_wHalf_prob,
    fun x => by norm_num [rit_wHalf], Finset.univ.powerset, Finset.univ.powerset, ?_⟩
  rw [rit_collapseLHS, rit_collapseRHS]; norm_num


omit [Fintype α] in

theorem rit_iterDownComp_append_singleton (cs : List α) (i : α) (𝒜 : Finset (Finset α)) :
    iterDownComp (cs ++ [i]) 𝒜 = iterDownComp cs (Down.compression i 𝒜) := by
  unfold iterDownComp; rw [List.foldr_append]; rfl

omit [Fintype α] in


theorem rit_exists_common_iterDownComp_isLowerSet (𝒜 ℬ : Finset (Finset α)) :
    ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
      ∧ IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α)) := by
  generalize hM : totalSize 𝒜 + totalSize ℬ = M
  induction M using Nat.strong_induction_on generalizing 𝒜 ℬ with
  | _ M ih =>
    by_cases hA : IsLowerSet (𝒜 : Set (Finset α))
    · by_cases hB : IsLowerSet (ℬ : Set (Finset α))
      · exact ⟨[], hA, hB⟩
      · rw [isLowerSet_iff_forall_downComp_eq_self, not_forall] at hB
        obtain ⟨i, hi⟩ := hB
        have hltB : totalSize (Down.compression i ℬ) < totalSize ℬ :=
          totalSize_downComp_lt i ℬ hi
        have hleA : totalSize (Down.compression i 𝒜) ≤ totalSize 𝒜 := totalSize_downComp_le i 𝒜
        have hlt : totalSize (Down.compression i 𝒜) + totalSize (Down.compression i ℬ) < M := by
          omega
        obtain ⟨cs, hcsA, hcsB⟩ := ih _ hlt (Down.compression i 𝒜) (Down.compression i ℬ) rfl
        exact ⟨cs ++ [i],
          by rw [rit_iterDownComp_append_singleton]; exact hcsA,
          by rw [rit_iterDownComp_append_singleton]; exact hcsB⟩
    · rw [isLowerSet_iff_forall_downComp_eq_self, not_forall] at hA
      obtain ⟨i, hi⟩ := hA
      have hltA : totalSize (Down.compression i 𝒜) < totalSize 𝒜 := totalSize_downComp_lt i 𝒜 hi
      have hleB : totalSize (Down.compression i ℬ) ≤ totalSize ℬ := totalSize_downComp_le i ℬ
      have hlt : totalSize (Down.compression i 𝒜) + totalSize (Down.compression i ℬ) < M := by
        omega
      obtain ⟨cs, hcsA, hcsB⟩ := ih _ hlt (Down.compression i 𝒜) (Down.compression i ℬ) rfl
      exact ⟨cs ++ [i],
        by rw [rit_iterDownComp_append_singleton]; exact hcsA,
        by rw [rit_iterDownComp_append_singleton]; exact hcsB⟩


end StatMech
