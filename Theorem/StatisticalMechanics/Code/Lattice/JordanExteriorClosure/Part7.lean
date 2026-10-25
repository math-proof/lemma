/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part7
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


theorem jec_rayCount_retPath (z : Site 2) (α a0 b0 c d : ℤ)
    (ha : α ≤ a0) (hb : α ≤ b0) (hcd : c ≤ d) :
    jec_rayCount z (jec_retPath α a0 b0 c d ha hb hcd) =
      (if b0 ≤ z 0 - 1 ∧ d ≤ z 1 - 1 ∧ z 1 - 1 ≤ d then 1 else 0)
      + (if α-1 ≤ z 0 - 1 ∧ c-1 ≤ z 1 - 1 ∧
            z 1 - 1 ≤ (c-1) + ((d+1-(c-1)).toNat:ℤ) - 1 then 1 else 0)
      + (if a0 ≤ z 0 - 1 ∧ c-1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ c-1 then 1 else 0) := by
  unfold jec_retPath
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse, jec_rayCount_vsegUp,
    jec_rayCount_hsegRight]
  push_cast
  have e1 : (if b0 ≤ z 0 - 1 ∧ d ≤ z 1 - 1 ∧ z 1 - 1 ≤ d + (1:ℤ) - 1 then (1:ℕ) else 0)
      = (if b0 ≤ z 0 - 1 ∧ d ≤ z 1 - 1 ∧ z 1 - 1 ≤ d then 1 else 0) := by
    congr 1; apply propext; constructor <;> (rintro ⟨a, b, c⟩; exact ⟨a, b, by omega⟩)
  have e3 : (if a0 ≤ z 0 - 1 ∧ c - 1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ c - 1 + (1:ℤ) - 1 then (1:ℕ) else 0)
      = (if a0 ≤ z 0 - 1 ∧ c - 1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ c - 1 then 1 else 0) := by
    congr 1; apply propext; constructor <;> (rintro ⟨a, b, c⟩; exact ⟨a, b, by omega⟩)
  rw [e1, e3]; ring


theorem jec_retPath_support (α a0 b0 c d : ℤ) (ha : α ≤ a0) (hb : α ≤ b0) (hcd : c ≤ d)
    {p : Site 2} (hp : p ∈ (jec_retPath α a0 b0 c d ha hb hcd).support) :
    p 0 = α - 1 ∨ p 1 = c - 1 ∨ p 1 = d + 1 ∨ p = ![b0, d] ∨ p = ![a0, c] := by
  unfold jec_retPath at hp
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
  rcases hp with h | h | h | h | h
  · obtain ⟨h0, h1, h2⟩ := jec_vsegUp_support b0 d 1 h
    push_cast at h2
    by_cases hpd : p 1 = d + 1
    · right; right; left; exact hpd
    · right; right; right; left
      have hp1 : p 1 = d := by omega
      ext i; fin_cases i
      · simpa using h0
      · simpa using hp1
  · obtain ⟨h1, _, _⟩ := jec_hsegRight_support (d+1) (α-1) _ h
    right; right; left; exact h1
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support (α-1) (c-1) _ h
    left; exact h0
  · obtain ⟨h1, _, _⟩ := jec_hsegRight_support (c-1) (α-1) _ h
    right; left; exact h1
  · obtain ⟨h0, h1, h2⟩ := jec_vsegUp_support a0 (c-1) 1 h
    push_cast at h2
    by_cases hpc : p 1 = c - 1
    · right; left; exact hpc
    · right; right; right; right
      have hp1 : p 1 = c := by omega
      ext i; fin_cases i
      · simpa using h0
      · simpa using hp1


theorem jec_retPath_col (α β a0 b0 c d : ℤ) (ha : α ≤ a0) (hb : α ≤ b0) (hcd : c ≤ d)
    (haβ : a0 ≤ β) (hbβ : b0 ≤ β) (hαβ : α ≤ β) {p : Site 2}
    (hp : p ∈ (jec_retPath α a0 b0 c d ha hb hcd).support) :
    α - 1 ≤ p 0 ∧ p 0 ≤ β := by
  unfold jec_retPath at hp
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
  rcases hp with h | h | h | h | h
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support b0 d 1 h; omega
  · obtain ⟨_, h0a, h0b⟩ := jec_hsegRight_support (d+1) (α-1) _ h
    rw [show ((b0 - (α-1)).toNat : ℤ) = b0 - (α-1) by omega] at h0b; omega
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support (α-1) (c-1) _ h; omega
  · obtain ⟨_, h0a, h0b⟩ := jec_hsegRight_support (c-1) (α-1) _ h
    rw [show ((a0 - (α-1)).toNat : ℤ) = a0 - (α-1) by omega] at h0b; omega
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support a0 (c-1) 1 h; omega


end Lattice
end StatMech
