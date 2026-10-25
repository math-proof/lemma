/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Def.StatisticalMechanics.Code.Walls.rc73seqcompress
set_option linter.style.longLine false

open Finset


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


@[simp] lemma rc73_mem_slice0 (i : α) (𝒜 : Finset (Finset α)) (s : Finset α) :
    s ∈ rc73_slice0 i 𝒜 ↔ s ∈ 𝒜 ∧ i ∉ s := by
  simp [rc73_slice0, mem_filter]


lemma rc73_mem_slice1 (i : α) (𝒜 : Finset (Finset α)) (s : Finset α) :
    s ∈ rc73_slice1 i 𝒜 ↔ insert i s ∈ 𝒜 ∧ i ∉ s := by
  simp only [rc73_slice1, mem_image, mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hit⟩, rfl⟩
    refine ⟨?_, notMem_erase _ _⟩
    rwa [insert_erase hit]
  · rintro ⟨hs, his⟩
    exact ⟨insert i s, ⟨hs, mem_insert_self _ _⟩, erase_insert his⟩


lemma rc73_slice1_notMem (i : α) (𝒜 : Finset (Finset α)) {s : Finset α}
    (hs : s ∈ rc73_slice1 i 𝒜) : i ∉ s := ((rc73_mem_slice1 i 𝒜 s).mp hs).2


lemma rc73_slice0_notMem (i : α) (𝒜 : Finset (Finset α)) {s : Finset α}
    (hs : s ∈ rc73_slice0 i 𝒜) : i ∉ s := ((rc73_mem_slice0 i 𝒜 s).mp hs).2


lemma rc73_card_present_eq_slice1 (i : α) (𝒜 : Finset (Finset α)) :
    (𝒜.filter (fun s => i ∈ s)).card = (rc73_slice1 i 𝒜).card := by
  unfold rc73_slice1
  rw [Finset.card_image_of_injOn]
  intro s hs t ht hst
  rw [Finset.mem_coe, Finset.mem_filter] at hs ht
  simp only at hst
  have : insert i (s.erase i) = insert i (t.erase i) := by rw [hst]
  rwa [insert_erase hs.2, insert_erase ht.2] at this


lemma rc73_card_eq_slices (i : α) (𝒜 : Finset (Finset α)) :
    𝒜.card = (rc73_slice0 i 𝒜).card + (rc73_slice1 i 𝒜).card := by
  rw [← rc73_card_present_eq_slice1]
  unfold rc73_slice0
  rw [add_comm, Finset.card_filter_add_card_filter_not (p := fun s => i ∈ s)]


end StatMech.Walls
