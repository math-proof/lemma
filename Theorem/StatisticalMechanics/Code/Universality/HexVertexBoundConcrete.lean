/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexVBC_vertexBound_false (a : ℂ) (h0 : ℤ) :
    ¬ (∀ W : HexWalk,
        (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
        ∀ x ∈ W.vertices,
          x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) := by
  intro hclosure
  set W : HexWalk := ⟨a, h0 + 1, []⟩ with hW
  have hmids : W.mids = [a] := by unfold HexWalk.mids; simp [hW]
  have hverts : W.vertices = [a + halfStep (h0 + 1)] := by
    unfold HexWalk.vertices; simp [hW]
  have hmem : ∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) := by
    rw [hmids]; intro m hm; simp only [List.mem_singleton] at hm; rw [hm]; simp
  have hconc := hclosure W hmem (a + halfStep (h0 + 1)) (by rw [hverts]; simp)
  have heq : a + halfStep (h0 + 1) = a + (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
    rw [hexConcrete_halfStep_add, hexConcrete_omega_cubic]; push_cast; ring
  rw [heq] at hconc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hconc
  have hs : halfStep h0 ≠ 0 := hexConcrete_halfStep_ne h0
  rcases hconc with h | h | h
  · rw [hexConcrete_v0_canon] at h
    exact hexConcrete_mid_ne a (halfStep h0) hs 1 1 1 0 (by norm_num) h
  · rw [hexConcrete_vq_canon] at h
    exact hexConcrete_mid_ne a (halfStep h0) hs 1 1 1 (-2) (by norm_num) h
  · rw [hexConcrete_vr_canon] at h
    exact hexConcrete_mid_ne a (halfStep h0) hs 1 1 3 2 (by norm_num) h


theorem hexVBC_vert_eq_mid_plus_step (m : ℂ) (h : ℤ) (ts : List ℤ) :
    ∀ x ∈ verticesAux m h ts, ∃ mm ∈ midsAux m h ts, ∃ hh : ℤ, x = mm + halfStep hh := by
  induction ts generalizing m h with
  | nil =>
    intro x hx
    simp only [verticesAux_nil, List.mem_singleton] at hx
    exact ⟨m, by simp, h, hx⟩
  | cons t ts ih =>
    intro x hx
    rw [verticesAux_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact ⟨m, by simp, h, hx⟩
    · obtain ⟨mm, hmm, hh, hxe⟩ := ih (m + halfStep h + halfStep (h + t)) (h + t) x hx
      exact ⟨mm, by rw [midsAux_cons, List.mem_cons]; exact Or.inr hmm, hh, hxe⟩


theorem hexVBC_halfStep_add6 (h : ℤ) : halfStep (h + 6) = halfStep h := by
  unfold halfStep
  rw [show (h + 6 : ℤ) = (h + 3) + 3 by ring, hexUnit_add_three, hexUnit_add_three]; ring


theorem hexVBC_step0 (h0 : ℤ) :
    halfStep (h0 + 0) = (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  push_cast; ring

theorem hexVBC_step1 (h0 : ℤ) :
    halfStep (h0 + 1) = (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_halfStep_add, hexConcrete_omega_cubic]; push_cast; ring

theorem hexVBC_step2 (h0 : ℤ) :
    halfStep (h0 + 2) = (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_halfStep_add2]; push_cast; ring

theorem hexVBC_step3 (h0 : ℤ) :
    halfStep (h0 + 3) = (((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold halfStep; rw [hexUnit_add_three]; push_cast; ring

theorem hexVBC_step4 (h0 : ℤ) :
    halfStep (h0 + 4) = (((-1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  have h1 : halfStep (h0 + 1) = (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 :=
    hexVBC_step1 h0
  unfold halfStep at h1 ⊢
  rw [show (h0 + 4 : ℤ) = (h0 + 1) + 3 by ring, hexUnit_add_three]
  rw [show ((1 : ℂ) / 2) * -hexUnit (h0 + 1) = -((1 / 2) * hexUnit (h0 + 1)) by ring, h1]
  push_cast; ring

theorem hexVBC_step5 (h0 : ℤ) :
    halfStep (h0 + 5) = (((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [show (h0 + 5 : ℤ) = (h0 - 1) + 6 by ring, hexVBC_halfStep_add6, hexConcrete_halfStep_sub]
  push_cast; ring


theorem hexVBC_halfStep_classify (h0 h : ℤ) :
    ∃ α β : ℝ, halfStep h = ((α : ℂ) + (β : ℂ) * hexOmega) * halfStep h0 ∧
      ((α, β) = ((1 : ℝ), (0 : ℝ)) ∨ (α, β) = (1, 1) ∨ (α, β) = (0, 1) ∨
       (α, β) = (-1, 0) ∨ (α, β) = (-1, -1) ∨ (α, β) = (0, -1)) := by
  set d := h - h0 with hd
  have hh : h = h0 + d := by rw [hd]; ring
  set r := d % 6 with hr
  have hrange : 0 ≤ r ∧ r < 6 :=
    ⟨Int.emod_nonneg d (by norm_num), Int.emod_lt_of_pos d (by norm_num)⟩
  have hdec : d = 6 * (d / 6) + r := by rw [hr]; omega
  have hper6 : ∀ (x : ℤ) (k : ℤ), halfStep (x + 6 * k) = halfStep x := by
    intro x k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        rw [show x + 6 * ((n : ℤ) + 1) = (x + 6 * (n : ℤ)) + 6 by ring, hexVBC_halfStep_add6]
        exact ih
    | pred n ih =>
        have hstep : halfStep ((x + 6 * (-(n : ℤ) - 1)) + 6) = halfStep (x + 6 * (-(n : ℤ) - 1)) :=
          hexVBC_halfStep_add6 _
        rw [show (x + 6 * (-(n : ℤ) - 1)) + 6 = x + 6 * (-(n : ℤ)) by ring] at hstep
        rw [← hstep]; exact ih
  have hperiod : halfStep h = halfStep (h0 + r) := by
    rw [hh, hdec, show h0 + (6 * (d / 6) + r) = (h0 + r) + 6 * (d / 6) by ring, hper6]
  obtain ⟨hr0, hr6⟩ := hrange
  interval_cases r
  · exact ⟨1, 0, by rw [hperiod, hexVBC_step0], by tauto⟩
  · exact ⟨1, 1, by rw [hperiod, hexVBC_step1], by tauto⟩
  · exact ⟨0, 1, by rw [hperiod, hexVBC_step2], by tauto⟩
  · exact ⟨-1, 0, by rw [hperiod, hexVBC_step3], by tauto⟩
  · exact ⟨-1, -1, by rw [hperiod, hexVBC_step4], by tauto⟩
  · exact ⟨0, -1, by rw [hperiod, hexVBC_step5], by tauto⟩


end StatMech.Universality
