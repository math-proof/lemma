/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Walls.kwd_crosscountparity.Part2
open Finset Set SimpleGraph
open StatMech.Lattice


namespace StatMech.Walls

@[simp] theorem kwd_sideBoundary_mk {V : Type*} (S : V → Bool) (x y : V) :
    kwd_sideBoundary S s(x, y) = (S x != S y) := rfl


theorem kwd_crossCount_parity {V : Type*} {G : SimpleGraph V} (S : V → Bool)
    {x y : V} (w : G.Walk x y) :
    Even (kwd_crossCount (kwd_sideBoundary S) w) ↔ (S x = S y) := by
  induction w with
  | nil => simp [kwd_crossCount]
  | @cons a b c hab p ih =>
    rw [kwd_crossCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
    rw [kwd_crossCount] at ih
    by_cases hbd : kwd_sideBoundary S s(a, b) = true
    · rw [if_pos hbd, Nat.even_add_one, ih]
      rw [kwd_sideBoundary_mk] at hbd
      cases ha : S a <;> cases hb : S b <;> cases hc : S c <;> simp_all
    · rw [if_neg hbd, add_zero, ih]
      rw [kwd_sideBoundary_mk] at hbd
      cases ha : S a <;> cases hb : S b <;> cases hc : S c <;> simp_all


theorem kwd_crossCount_parity_eq_of_sameEndpoints {V : Type*} {G : SimpleGraph V}
    (S : V → Bool) {x y : V} (w₁ w₂ : G.Walk x y) :
    kwd_crossCount (kwd_sideBoundary S) w₁ % 2
      = kwd_crossCount (kwd_sideBoundary S) w₂ % 2 := by
  have h1 := kwd_crossCount_parity S w₁
  have h2 := kwd_crossCount_parity S w₂
  rw [Nat.even_iff] at h1 h2
  by_cases hP : S x = S y
  · rw [h1.mpr hP, h2.mpr hP]
  · have e1 : kwd_crossCount (kwd_sideBoundary S) w₁ % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one _ with h | h
      · exact absurd (h1.mp h) hP
      · exact h
    have e2 : kwd_crossCount (kwd_sideBoundary S) w₂ % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one _ with h | h
      · exact absurd (h2.mp h) hP
      · exact h
    rw [e1, e2]


theorem kwd_crossCount_even_of_closed {V : Type*} {G : SimpleGraph V} (S : V → Bool)
    {x : V} (w : G.Walk x x) :
    Even (kwd_crossCount (kwd_sideBoundary S) w) :=
  (kwd_crossCount_parity S w).mpr rfl


end StatMech.Walls
