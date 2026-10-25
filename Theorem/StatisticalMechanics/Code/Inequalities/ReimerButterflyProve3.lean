/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem erase_mem_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) {s : Finset α} (hs : s ∈ 𝒜) (i : α) :
    s.erase i ∈ 𝒜 := by
  have : (s.erase i : Finset α) ≤ s := Finset.erase_subset _ _
  exact h this hs


theorem downComp_eq_self_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) (i : α) :
    Down.compression i 𝒜 = 𝒜 := by
  ext s
  rw [Down.mem_compression]
  constructor
  · rintro (⟨hs, _⟩ | ⟨_, hins⟩)
    · exact hs
    · 
      exact h (Finset.subset_insert i s) hins
  · intro hs
    exact Or.inl ⟨hs, erase_mem_of_isLowerSet h hs i⟩


theorem downComp_idem (i : α) (𝒜 : Finset (Finset α)) :
    Down.compression i (Down.compression i 𝒜) = Down.compression i 𝒜 :=
  Down.compression_idem i 𝒜


end StatMech
