/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.StraightWalk
open Set
open SimpleGraph


namespace StatMech

namespace Lattice

theorem sw_horizR_support_eq (y x0 : ℤ) (m : ℕ) :
    (sw_horizR y x0 (m + 1)).support
      = (sw_horizR y x0 m).support ++ [![x0 + (m : ℤ) + 1, y]] := by
  show ((sw_horizR y x0 m).append _).support = _
  rw [Walk.support_append, Walk.support_copy, Walk.support_cons, Walk.support_nil]
  rfl


theorem sw_vertU_support_eq (x y0 : ℤ) (m : ℕ) :
    (sw_vertU x y0 (m + 1)).support
      = (sw_vertU x y0 m).support ++ [![x, y0 + (m : ℤ) + 1]] := by
  show ((sw_vertU x y0 m).append _).support = _
  rw [Walk.support_append, Walk.support_copy, Walk.support_cons, Walk.support_nil]
  rfl


theorem sw_horizR_mem_support (y x0 : ℤ) (n : ℕ) (z : Site 2) :
    z ∈ (sw_horizR y x0 n).support
      ↔ ∃ t : ℤ, 0 ≤ t ∧ t ≤ (n : ℤ) ∧ z = ![x0 + t, y] := by
  induction n with
  | zero =>
    simp only [sw_horizR, Walk.support_copy, Walk.support_nil, List.mem_singleton]
    constructor
    · intro h; exact ⟨0, le_refl _, by norm_num, by rw [h]; norm_num⟩
    · rintro ⟨t, ht0, htn, rfl⟩
      have : t = 0 := le_antisymm (by exact_mod_cast htn) ht0
      simp [this]
  | succ m ih =>
    rw [sw_horizR_support_eq, List.mem_append, List.mem_singleton, ih]
    push_cast
    constructor
    · rintro (⟨t, ht0, htm, rfl⟩ | rfl)
      · exact ⟨t, ht0, by linarith, rfl⟩
      · exact ⟨(m : ℤ) + 1, by positivity, le_refl _, by norm_num [add_assoc]⟩
    · rintro ⟨t, ht0, htm, rfl⟩
      rcases eq_or_lt_of_le htm with h | h
      · right; rw [h]; ring_nf
      · left; exact ⟨t, ht0, by linarith, rfl⟩


theorem sw_vertU_mem_support (x y0 : ℤ) (n : ℕ) (z : Site 2) :
    z ∈ (sw_vertU x y0 n).support
      ↔ ∃ t : ℤ, 0 ≤ t ∧ t ≤ (n : ℤ) ∧ z = ![x, y0 + t] := by
  induction n with
  | zero =>
    simp only [sw_vertU, Walk.support_copy, Walk.support_nil, List.mem_singleton]
    constructor
    · intro h; exact ⟨0, le_refl _, by norm_num, by rw [h]; norm_num⟩
    · rintro ⟨t, ht0, htn, rfl⟩
      have : t = 0 := le_antisymm (by exact_mod_cast htn) ht0
      simp [this]
  | succ m ih =>
    rw [sw_vertU_support_eq, List.mem_append, List.mem_singleton, ih]
    push_cast
    constructor
    · rintro (⟨t, ht0, htm, rfl⟩ | rfl)
      · exact ⟨t, ht0, by linarith, rfl⟩
      · exact ⟨(m : ℤ) + 1, by positivity, le_refl _, by norm_num [add_assoc]⟩
    · rintro ⟨t, ht0, htm, rfl⟩
      rcases eq_or_lt_of_le htm with h | h
      · right; rw [h]; ring_nf
      · left; exact ⟨t, ht0, by linarith, rfl⟩


theorem sw_horizR_support_nodup (y x0 : ℤ) (n : ℕ) :
    (sw_horizR y x0 n).support.Nodup := by
  induction n with
  | zero => simp [sw_horizR]
  | succ m ih =>
    rw [sw_horizR_support_eq, List.nodup_append]
    refine ⟨ih, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rw [sw_horizR_mem_support] at ha
    obtain ⟨t, ht0, htm, heq⟩ := ha
    intro hcontra
    rw [heq] at hcontra
    have hx : x0 + t = x0 + (m : ℤ) + 1 := by
      have := congrFun hcontra 0; simpa using this
    linarith


theorem sw_vertU_support_nodup (x y0 : ℤ) (n : ℕ) :
    (sw_vertU x y0 n).support.Nodup := by
  induction n with
  | zero => simp [sw_vertU]
  | succ m ih =>
    rw [sw_vertU_support_eq, List.nodup_append]
    refine ⟨ih, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rw [sw_vertU_mem_support] at ha
    obtain ⟨t, ht0, htm, heq⟩ := ha
    intro hcontra
    rw [heq] at hcontra
    have hy : y0 + t = y0 + (m : ℤ) + 1 := by
      have := congrFun hcontra 1; simpa using this
    linarith


end Lattice
end StatMech
