/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part3
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem totalSize_downComp_le (i : α) (𝒜 : Finset (Finset α)) :
    totalSize (Down.compression i 𝒜) ≤ totalSize 𝒜 := by
  unfold totalSize
  rw [downComp_eq_image_cmap, Finset.sum_image (fun s hs t ht => cmap_injOn i 𝒜 hs ht)]
  exact Finset.sum_le_sum (fun s _ => cmap_card_le i 𝒜 s)


theorem totalSize_downComp_lt (i : α) (𝒜 : Finset (Finset α))
    (hne : Down.compression i 𝒜 ≠ 𝒜) :
    totalSize (Down.compression i 𝒜) < totalSize 𝒜 := by
  have hexists : ∃ s ∈ 𝒜, i ∈ s ∧ s.erase i ∉ 𝒜 := by
    by_contra hc
    refine hne ((downComp_eq_self_iff i 𝒜).2 (fun s hs => ?_))
    by_cases hi : i ∈ s
    · by_contra hcerase
      exact hc ⟨s, hs, hi, hcerase⟩
    · rwa [erase_eq_of_notMem hi]
  obtain ⟨s, hs, hisin, herasenot⟩ := hexists
  unfold totalSize
  rw [downComp_eq_image_cmap, Finset.sum_image (fun a ha b hb => cmap_injOn i 𝒜 ha hb)]
  refine Finset.sum_lt_sum (fun a _ => cmap_card_le i 𝒜 a) ⟨s, hs, ?_⟩
  unfold cmap
  rw [if_pos ⟨hisin, herasenot⟩]
  exact card_erase_lt_of_mem hisin


theorem exists_iterDownComp_isLowerSet (𝒜 : Finset (Finset α)) :
    ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) := by
  generalize hM : totalSize 𝒜 = M
  induction M using Nat.strong_induction_on generalizing 𝒜 with
  | _ M ih =>
    by_cases hLow : IsLowerSet (𝒜 : Set (Finset α))
    · exact ⟨[], hLow⟩
    · rw [isLowerSet_iff_forall_downComp_eq_self] at hLow
      rw [not_forall] at hLow
      obtain ⟨i, hi⟩ := hLow
      have hlt : totalSize (Down.compression i 𝒜) < M := hM ▸ totalSize_downComp_lt i 𝒜 hi
      obtain ⟨cs, hcs⟩ :=
        ih (totalSize (Down.compression i 𝒜)) hlt (Down.compression i 𝒜) rfl
      refine ⟨cs ++ [i], ?_⟩
      have hfold : iterDownComp (cs ++ [i]) 𝒜 = iterDownComp cs (Down.compression i 𝒜) := by
        unfold iterDownComp; rw [List.foldr_append]; rfl
      rw [hfold]; exact hcs


theorem exists_dpairsCount_le_endpoint (𝒜 : Finset (Finset α)) :
    ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
      ∧ dpairsCount 𝒜 𝒜 ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs 𝒜) := by
  obtain ⟨cs, hcs⟩ := exists_iterDownComp_isLowerSet 𝒜
  exact ⟨cs, hcs, dpairsCount_iterDownComp_mono cs 𝒜 𝒜⟩


end StatMech
