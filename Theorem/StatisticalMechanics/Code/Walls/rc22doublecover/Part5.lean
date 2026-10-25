/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Walls.rc22doublecover.Part5
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


variable {β : Type*} [DecidableEq β]


theorem rc22_traceClosed_iff_of_lowerSet {𝒜 : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (K S : Finset α) :
    (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ↔ (S ∪ Kᶜ) ∈ 𝒜 := by
  constructor
  · intro h
    apply h
    ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
    constructor
    · rintro ⟨hx | hx, hxK⟩
      · exact ⟨hx, hxK⟩
      · exact absurd hxK hx
    · rintro ⟨hxS, hxK⟩; exact ⟨Or.inl hxS, hxK⟩
  · intro hmem T hT
    have hsub : T ⊆ S ∪ Kᶜ := by
      intro x hxT
      simp only [Finset.mem_union, Finset.mem_compl]
      by_cases hxK : x ∈ K
      · left
        have : x ∈ T ∩ K := Finset.mem_inter.mpr ⟨hxT, hxK⟩
        rw [hT] at this
        exact (Finset.mem_inter.mp this).1
      · right; exact hxK
    exact h𝒜 hsub hmem

open Classical in


theorem rc22_mem_famCylBox_of_lowerSet {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) (S : Finset α) :
    S ∈ rc20_famCylBox 𝒜 ℬ ↔
      ∃ K L : Finset α, Disjoint K L ∧ (S ∪ Kᶜ) ∈ 𝒜 ∧ (S ∪ Lᶜ) ∈ ℬ := by
  rw [rc21_mem_famCylBox]
  refine exists_congr fun K => exists_congr fun L => ?_
  rw [rc22_traceClosed_iff_of_lowerSet h𝒜, rc22_traceClosed_iff_of_lowerSet hℬ]

end StatMech.Walls
