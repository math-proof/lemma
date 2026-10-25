/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


theorem hexStrip_vert_eq_mid_plus_step (m : ℂ) (h : ℤ) (ts : List ℤ) :
    ∀ x ∈ verticesAux m h ts, ∃ mm ∈ midsAux m h ts, ∃ hh : ℤ, x = mm + halfStep hh := by
  induction ts generalizing m h with
  | nil =>
    intro x hx
    simp only [verticesAux_nil, List.mem_singleton] at hx
    exact ⟨m, by simp [midsAux_nil], h, hx⟩
  | cons t ts ih =>
    intro x hx
    rw [verticesAux_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact ⟨m, by simp [midsAux_cons], h, hx⟩
    · obtain ⟨mm, hmm, hh, hxe⟩ := ih (m + halfStep h + halfStep (h + t)) (h + t) x hx
      exact ⟨mm, by rw [midsAux_cons, List.mem_cons]; exact Or.inr hmm, hh, hxe⟩


theorem hexStrip_vertex_mem_eq (w : HexWalk) :
    ∀ x ∈ w.vertices, ∃ mm ∈ w.mids, ∃ hh : ℤ, x = mm + halfStep hh := by
  intro x hx
  exact hexStrip_vert_eq_mid_plus_step w.startMid w.h0 w.turns x hx


theorem hexStrip_halfStep_add6 (h : ℤ) : halfStep (h + 6) = halfStep h := by
  unfold halfStep
  rw [show (h + 6 : ℤ) = (h + 3) + 3 by ring, hexUnit_add_three, hexUnit_add_three]; ring


theorem hexStrip_halfStep_mod6 (h : ℤ) : halfStep h = halfStep (h % 6) := by
  have hper6 : ∀ (x : ℤ) (k : ℤ), halfStep (x + 6 * k) = halfStep x := by
    intro x k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        rw [show x + 6 * ((n : ℤ) + 1) = (x + 6 * (n : ℤ)) + 6 by ring, hexStrip_halfStep_add6]
        exact ih
    | pred n ih =>
        have hh : halfStep ((x + 6 * (-(n : ℤ) - 1)) + 6) = halfStep (x + 6 * (-(n : ℤ) - 1)) :=
          hexStrip_halfStep_add6 _
        rw [show (x + 6 * (-(n : ℤ) - 1)) + 6 = x + 6 * (-(n : ℤ)) by ring] at hh
        rw [← hh]; exact ih
  conv_lhs => rw [show h = (h % 6) + 6 * (h / 6) by omega]
  rw [hper6]


@[simp]
theorem hexStrip_norm_halfStep (h : ℤ) : ‖halfStep h‖ = 1 / 2 := by
  unfold halfStep
  rw [norm_mul, norm_hexUnit, mul_one]
  norm_num


theorem hexStrip_dist_vert_mid (mm : ℂ) (hh : ℤ) : dist (mm + halfStep hh) mm = 1 / 2 := by
  rw [Complex.dist_eq, add_sub_cancel_left, hexStrip_norm_halfStep]


end StatMech.Universality
