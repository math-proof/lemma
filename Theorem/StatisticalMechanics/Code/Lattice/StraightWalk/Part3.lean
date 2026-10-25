/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.StraightWalk.Part2
open Set
open SimpleGraph


namespace StatMech

namespace Lattice

theorem sw_horizSeg_mem_support (y x0 x1 : ℤ) (z : Site 2) :
    z ∈ (sw_horizSeg y x0 x1).support
      ↔ ∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y] := by
  unfold sw_horizSeg
  by_cases h : x0 ≤ x1
  · rw [dif_pos h, Walk.support_copy, sw_horizR_mem_support, Set.uIcc_of_le h]
    constructor
    · rintro ⟨t, ht0, htn, rfl⟩
      rw [Int.toNat_of_nonneg (by linarith)] at htn
      exact ⟨x0 + t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      refine ⟨s - x0, by linarith, ?_, by ring_nf⟩
      rw [Int.toNat_of_nonneg (by linarith)]; linarith
  · have hle : x1 ≤ x0 := le_of_lt (lt_of_not_ge h)
    rw [dif_neg h, Walk.support_copy, Walk.support_reverse, List.mem_reverse,
      sw_horizR_mem_support, Set.uIcc_of_ge hle]
    constructor
    · rintro ⟨t, ht0, htn, rfl⟩
      rw [Int.toNat_of_nonneg (by linarith)] at htn
      exact ⟨x1 + t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs0⟩, rfl⟩
      refine ⟨s - x1, by linarith, ?_, by ring_nf⟩
      rw [Int.toNat_of_nonneg (by linarith)]; linarith


theorem sw_vertSeg_mem_support (x y0 y1 : ℤ) (z : Site 2) :
    z ∈ (sw_vertSeg x y0 y1).support
      ↔ ∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x, t] := by
  unfold sw_vertSeg
  by_cases h : y0 ≤ y1
  · rw [dif_pos h, Walk.support_copy, sw_vertU_mem_support, Set.uIcc_of_le h]
    constructor
    · rintro ⟨t, ht0, htn, rfl⟩
      rw [Int.toNat_of_nonneg (by linarith)] at htn
      exact ⟨y0 + t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      refine ⟨s - y0, by linarith, ?_, by ring_nf⟩
      rw [Int.toNat_of_nonneg (by linarith)]; linarith
  · have hle : y1 ≤ y0 := le_of_lt (lt_of_not_ge h)
    rw [dif_neg h, Walk.support_copy, Walk.support_reverse, List.mem_reverse,
      sw_vertU_mem_support, Set.uIcc_of_ge hle]
    constructor
    · rintro ⟨t, ht0, htn, rfl⟩
      rw [Int.toNat_of_nonneg (by linarith)] at htn
      exact ⟨y1 + t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs0⟩, rfl⟩
      refine ⟨s - y1, by linarith, ?_, by ring_nf⟩
      rw [Int.toNat_of_nonneg (by linarith)]; linarith


theorem sw_seg_support_mem (y x0 x1 a b : ℤ) :
    (![a, b] : Site 2) ∈ (sw_horizSeg y x0 x1).support
      ↔ b = y ∧ a ∈ Set.uIcc x0 x1 := by
  rw [sw_horizSeg_mem_support]
  constructor
  · rintro ⟨t, ht, heq⟩
    have ha : a = t := by have := congrFun heq 0; simpa using this
    have hb : b = y := by have := congrFun heq 1; simpa using this
    exact ⟨hb, ha ▸ ht⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩


theorem sw_horizSeg_support_subset (y x0 x1 : ℤ) :
    {z : Site 2 | z ∈ (sw_horizSeg y x0 x1).support}
      ⊆ (fun t => (![t, y] : Site 2)) '' Set.uIcc x0 x1 := by
  intro z hz
  rw [Set.mem_setOf_eq, sw_horizSeg_mem_support] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact ⟨t, ht, rfl⟩


theorem sw_vertSeg_support_subset (x y0 y1 : ℤ) :
    {z : Site 2 | z ∈ (sw_vertSeg x y0 y1).support}
      ⊆ (fun t => (![x, t] : Site 2)) '' Set.uIcc y0 y1 := by
  intro z hz
  rw [Set.mem_setOf_eq, sw_vertSeg_mem_support] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact ⟨t, ht, rfl⟩


theorem sw_horizSeg_support_nodup (y x0 x1 : ℤ) :
    (sw_horizSeg y x0 x1).support.Nodup := by
  unfold sw_horizSeg
  by_cases h : x0 ≤ x1
  · rw [dif_pos h, Walk.support_copy]; exact sw_horizR_support_nodup _ _ _
  · rw [dif_neg h, Walk.support_copy, Walk.support_reverse, List.nodup_reverse]
    exact sw_horizR_support_nodup _ _ _


theorem sw_vertSeg_support_nodup (x y0 y1 : ℤ) :
    (sw_vertSeg x y0 y1).support.Nodup := by
  unfold sw_vertSeg
  by_cases h : y0 ≤ y1
  · rw [dif_pos h, Walk.support_copy]; exact sw_vertU_support_nodup _ _ _
  · rw [dif_neg h, Walk.support_copy, Walk.support_reverse, List.nodup_reverse]
    exact sw_vertU_support_nodup _ _ _


theorem sw_seg_nodup_of_distinct (y x0 x1 : ℤ) (hne : x0 ≠ x1) :
    (sw_horizSeg y x0 x1).support.Nodup ∧ (![x0, y] : Site 2) ≠ ![x1, y] := by
  refine ⟨sw_horizSeg_support_nodup y x0 x1, ?_⟩
  intro hcontra
  exact hne (by have := congrFun hcontra 0; simpa using this)


end Lattice
end StatMech
