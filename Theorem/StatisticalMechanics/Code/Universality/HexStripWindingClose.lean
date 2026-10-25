/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part7


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexUmlauf_runningHead_step_le (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW) (k : ℕ) (hk : k < ts.length) :
    |hexStripWinding_runningHead h0 ts (k + 1) - hexStripWinding_runningHead h0 ts k| ≤ 1 := by
  rw [hexStripWinding_runningHead_succ h0 ts k hk]
  have hmem : ts[k] ∈ ts := List.getElem_mem hk
  have hpm : ts[k] = 1 ∨ ts[k] = -1 :=
    hlegal.1 ts[k] (by rw [HexWalk.ofTurns_turns]; exact hmem)
  rcases hpm with h | h <;>
    rw [show hexStripWinding_runningHead h0 ts k + ts[k]
          - hexStripWinding_runningHead h0 ts k = ts[k] from by ring, h] <;>
    decide


theorem hexUmlauf_runningHead_IVT (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    ∀ i j : ℕ, i ≤ j → j ≤ ts.length → ∀ m : ℤ,
      min (hexStripWinding_runningHead h0 ts i) (hexStripWinding_runningHead h0 ts j) ≤ m →
      m ≤ max (hexStripWinding_runningHead h0 ts i) (hexStripWinding_runningHead h0 ts j) →
      ∃ c, i ≤ c ∧ c ≤ j ∧ hexStripWinding_runningHead h0 ts c = m := by
  
  set f := fun k => hexStripWinding_runningHead h0 ts k with hf
  intro i j hij hjlen
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d generalizing i with
  | zero =>
    intro m hlo hhi
    simp only [add_zero, min_self, max_self] at hlo hhi
    exact ⟨i, le_refl _, le_refl _, le_antisymm hlo hhi⟩
  | succ d ih =>
    intro m hlo hhi
    by_cases hcase : min (f i) (f (i + d)) ≤ m ∧ m ≤ max (f i) (f (i + d))
    · obtain ⟨c, hci, hcd, hcm⟩ := ih i (by omega) m hcase.1 hcase.2
      exact ⟨c, hci, by omega, hcm⟩
    · 
      
      have hidlt : i + d < ts.length := by omega
      have hs : |f (i + (d + 1)) - f (i + d)| ≤ 1 := by
        have hstep := hexUmlauf_runningHead_step_le a h0 ts hlegal (i + d) hidlt
        have e1 : i + d + 1 = i + (d + 1) := by ring
        rw [e1] at hstep
        exact hstep
      refine ⟨i + (d + 1), by omega, le_refl _, ?_⟩
      change f (i + (d + 1)) = m
      rw [abs_le] at hs
      rw [not_and_or, not_le, not_le] at hcase
      have hmm := min_choice (f i) (f (i + d))
      have hMM := max_choice (f i) (f (i + d))
      have hmm' := min_choice (f i) (f (i + (d + 1)))
      have hMM' := max_choice (f i) (f (i + (d + 1)))
      rcases hmm with h | h <;> rcases hMM with h2 | h2 <;>
        rcases hmm' with h3 | h3 <;> rcases hMM' with h4 | h4 <;>
        rw [h] at hcase <;> rw [h2] at hcase <;> rw [h3] at hlo <;> rw [h4] at hhi <;>
        omega


theorem hexUmlauf_window_of_wall_noFullTurn (a : ℂ) (h0 : ℤ) (ts : List ℤ) (w : ℤ)
    (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW)
    (hwall : ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k)
    (hnofull : ∀ k, k ≤ ts.length → hexStripWinding_runningHead h0 ts k ≠ w + 6)
    (hanchor : hexStripWinding_runningHead h0 ts 0 < w + 6) :
    ∀ k, k ≤ ts.length →
      w ≤ hexStripWinding_runningHead h0 ts k
        ∧ hexStripWinding_runningHead h0 ts k < w + 6 := by
  intro k hk
  refine ⟨hwall k hk, ?_⟩
  by_contra hge
  rw [not_lt] at hge
  set f := fun n => hexStripWinding_runningHead h0 ts n with hf
  have hf0 : f 0 < w + 6 := hanchor
  have hfk : w + 6 ≤ f k := hge
  
  have hm1 : min (f 0) (f k) ≤ w + 6 := by
    rcases le_total (f 0) (f k) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  have hm2 : w + 6 ≤ max (f 0) (f k) := by
    rcases le_total (f 0) (f k) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  obtain ⟨c, _hc0, hck, hcm⟩ :=
    hexUmlauf_runningHead_IVT a h0 ts hlegal 0 k (Nat.zero_le k) hk (w + 6) hm1 hm2
  exact hnofull c (by omega) hcm


end StatMech.Universality
