/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part2


namespace StatMech.Universality

open HexWalk

theorem hexEndpoint_mem_sawFinset (a : ℂ) (h0 : ℤ) (n : ℕ) (ts : List ℤ) :
    ts ∈ hexEndpointSAWFinset a h0 n ↔
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧ ts.length = n := by
  classical
  cases n with
  | zero =>
      simp only [hexEndpointSAWFinset, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨endpoint_nil_isLegalSAW a h0, rfl⟩
      · rintro ⟨_, hlen⟩
        exact List.length_eq_zero_iff.mp hlen
  | succ n =>
      simp only [hexEndpointSAWFinset, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
        · have hb := (hlc_mem_sawFinset a h0 n s).mp hs
          refine ⟨(endpointIsLegalSAW_append_one_iff a h0 s 1).2
            ⟨hb.1, Or.inl rfl⟩, ?_⟩
          simp [hb.2]
        · have hb := (hlc_mem_sawFinset a h0 n s).mp hs
          refine ⟨(endpointIsLegalSAW_append_one_iff a h0 s (-1)).2
            ⟨hb.1, Or.inr rfl⟩, ?_⟩
          simp [hb.2]
      · rintro ⟨hlegal, hlen⟩
        induction ts using List.reverseRecOn with
        | nil => simp at hlen
        | append_singleton s t _ =>
            have hdata := (endpointIsLegalSAW_append_one_iff a h0 s t).mp hlegal
            have hslen : s.length = n := by simp at hlen; omega
            have hs : s ∈ hlc_sawFinset a h0 n :=
              (hlc_mem_sawFinset a h0 n s).2 ⟨hdata.1, hslen⟩
            rcases hdata.2 with rfl | rfl
            · exact Or.inl ⟨s, hs, rfl⟩
            · exact Or.inr ⟨s, hs, rfl⟩

@[simp]
theorem hexEndpointSAWCount_zero (a : ℂ) (h0 : ℤ) :
    hexEndpointSAWCount a h0 0 = 1 := by
  simp [hexEndpointSAWCount, hexEndpointSAWFinset]

theorem hexEndpoint_append_one_injective (t : ℤ) :
    Function.Injective (fun ts : List ℤ => ts ++ [t]) :=
  List.append_left_injective [t]

theorem hexEndpoint_extension_images_disjoint (a : ℂ) (h0 : ℤ) (n : ℕ) :
    Disjoint
      ((hlc_sawFinset a h0 n).image (fun ts => ts ++ [(1 : ℤ)]))
      ((hlc_sawFinset a h0 n).image (fun ts => ts ++ [(-1 : ℤ)])) := by
  classical
  rw [Finset.disjoint_left]
  intro u hu hp
  rcases Finset.mem_image.mp hu with ⟨s, _, rfl⟩
  rcases Finset.mem_image.mp hp with ⟨r, _, heq⟩
  have hlast := congrArg List.getLast? heq
  simp at hlast


theorem hexEndpointSAWCount_succ (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hexEndpointSAWCount a h0 (n + 1) = 2 * hlc_sawCount a h0 n := by
  classical
  unfold hexEndpointSAWCount
  rw [hexEndpointSAWFinset, Finset.card_union_of_disjoint
    (hexEndpoint_extension_images_disjoint a h0 n)]
  rw [Finset.card_image_of_injective _ (hexEndpoint_append_one_injective 1),
    Finset.card_image_of_injective _ (hexEndpoint_append_one_injective (-1)),
    hlc_card_sawFinset]
  omega


end StatMech.Universality
