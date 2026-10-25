/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Def.StatisticalMechanics.Code.Walls.wndwinding
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wnd_signStep_mem (z u v : Site 2) :
    wnd_signStep z u v = 1 ∨ wnd_signStep z u v = 0 ∨ wnd_signStep z u v = -1 := by
  classical
  unfold wnd_signStep; split_ifs <;> simp

theorem wnd_abs_signStep_le_one (z u v : Site 2) : |wnd_signStep z u v| ≤ 1 := by
  rcases wnd_signStep_mem z u v with h | h | h <;> rw [h] <;> decide


theorem wnd_signStep_ne_zero_iff (z u v : Site 2) :
    wnd_signStep z u v ≠ 0 ↔ jec_rayEdge z s(u, v) := by
  classical
  rw [jec_rayEdge_mk]
  unfold wnd_signStep
  constructor
  · intro h
    split_ifs at h with h1 h2
    · exact ⟨h1.1, Or.inl ⟨h1.2.1, h1.2.2⟩⟩
    · exact ⟨h2.1, Or.inr ⟨by omega, by omega⟩⟩
    · exact absurd rfl h
  · rintro ⟨⟨hc, hle⟩, hcase⟩
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos ⟨⟨hc, hle⟩, h1, h2⟩]; decide
    · by_cases hup : (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1
      · rw [if_pos hup]; decide
      · rw [if_neg hup, if_pos ⟨⟨hc, hle⟩, h2, h1⟩]; decide

open Classical in


theorem wnd_abs_signStep_eq_indicator (z u v : Site 2) :
    |wnd_signStep z u v| = (if jec_rayEdge z s(u, v) then 1 else 0) := by
  classical
  by_cases h : jec_rayEdge z s(u, v)
  · rw [if_pos h]
    have hne := (wnd_signStep_ne_zero_iff z u v).mpr h
    rcases wnd_signStep_mem z u v with h1 | h1 | h1
    · rw [h1]; decide
    · exact absurd h1 hne
    · rw [h1]; decide
  · rw [if_neg h]
    have : wnd_signStep z u v = 0 := by
      by_contra hc; exact h ((wnd_signStep_ne_zero_iff z u v).mp hc)
    rw [this]; decide

open Classical in


theorem wnd_signStep_parity (z u v : Site 2) :
    wnd_signStep z u v % 2 = (if jec_rayEdge z s(u, v) then (1 : ℤ) else 0) % 2 := by
  classical
  by_cases h : jec_rayEdge z s(u, v)
  · rw [if_pos h]
    have hne := (wnd_signStep_ne_zero_iff z u v).mpr h
    rcases wnd_signStep_mem z u v with h1 | h1 | h1
    · rw [h1]
    · exact absurd h1 hne
    · rw [h1]; decide
  · rw [if_neg h]
    have : wnd_signStep z u v = 0 := by
      by_contra hc; exact h ((wnd_signStep_ne_zero_iff z u v).mp hc)
    rw [this]


theorem wnd_signStep_swap (z u v : Site 2) :
    wnd_signStep z v u = - wnd_signStep z u v := by
  classical
  unfold wnd_signStep
  split_ifs <;> omega


end Lattice
end StatMech
