/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.BaseCase
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind
import Def.StatisticalMechanics.Code.Onsager.WalkCrossing.Part2


namespace StatMech.Onsager.WalkCrossing

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


theorem upDown_card_eq (d : Fin n → Fin 4) (_hclosed : ∑ i, stepOf (d i) = 0) (m : ℤ) :
    (Finset.univ.filter
        (fun k : Fin n => (pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2)).card
      = (Finset.univ.filter
        (fun k : Fin n => m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m)).card := by
  classical
  set g : Fin n → ℤ := fun k => if m + 1 ≤ (pos d k).2 then (1 : ℤ) else 0 with hg
  
  have hshift : (∑ k : Fin n, g (k + 1)) = ∑ k, g k :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n)) g
  have htel : (∑ k : Fin n, (g (k + 1) - g k)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  
  have hper : ∀ k : Fin n, g (k + 1) - g k
      = (if ((pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2) then (1 : ℤ) else 0)
        - (if (m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m) then (1 : ℤ) else 0) := by
    intro k
    simp only [hg]
    split_ifs <;> omega
  
  have hsum : (∑ k : Fin n,
        ((if ((pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2) then (1 : ℤ) else 0)
          - (if (m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m) then (1 : ℤ) else 0))) = 0 := by
    have hcong : (∑ k : Fin n,
        ((if ((pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2) then (1 : ℤ) else 0)
          - (if (m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m) then (1 : ℤ) else 0)))
        = ∑ k : Fin n, (g (k + 1) - g k) :=
      Finset.sum_congr rfl (fun k _ => (hper k).symm)
    rw [hcong]; exact htel
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, sub_eq_zero] at hsum
  exact_mod_cast hsum


theorem fullLineCross_even (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (m : ℤ) :
    Even (fullLineCross d m) := by
  classical
  
  set Pup : Fin n → Prop := fun k => (pos d k).2 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).2 with hPup
  set Pdown : Fin n → Prop := fun k => m + 1 ≤ (pos d k).2 ∧ (pos d (k + 1)).2 ≤ m with hPdown
  have hiff : ∀ k : Fin n,
      (isVertEdge (d k) ∧ min ((pos d k).2) ((pos d (k + 1)).2) = m) ↔ (Pup k ∨ Pdown k) := by
    intro k
    simp only [hPup, hPdown]
    constructor
    · rintro ⟨hv, hmin⟩
      rcases vert_y_step d hclosed k hv with h | h <;> rw [h] at hmin ⊢ <;> omega
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · 
        rcases snd_step_bound d hclosed k with h | h | h
        · omega
        · refine ⟨?_, by rw [h]; omega⟩
          
          rcases show isVertEdge (d k) ∨ isHorizEdge (d k) from by
            rcases stepOf_coords (d k) with ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩
            · exact Or.inr (Or.inl hd)
            · exact Or.inl (Or.inl hd)
            · exact Or.inr (Or.inr hd)
            · exact Or.inl (Or.inr hd) with hvv | hhh
          · exact hvv
          · exact absurd (horiz_y_const d hclosed k hhh) (by omega)
        · omega
      · rcases snd_step_bound d hclosed k with h | h | h
        · omega
        · omega
        · refine ⟨?_, by rw [h]; omega⟩
          rcases show isVertEdge (d k) ∨ isHorizEdge (d k) from by
            rcases stepOf_coords (d k) with ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩
            · exact Or.inr (Or.inl hd)
            · exact Or.inl (Or.inl hd)
            · exact Or.inr (Or.inr hd)
            · exact Or.inl (Or.inr hd) with hvv | hhh
          · exact hvv
          · exact absurd (horiz_y_const d hclosed k hhh) (by omega)
  have hdisj : Disjoint (Finset.univ.filter Pup) (Finset.univ.filter Pdown) := by
    rw [Finset.disjoint_filter]
    intro k _ hup hdown
    simp only [hPup] at hup; simp only [hPdown] at hdown; omega
  have hsplit : (Finset.univ.filter (fun k : Fin n =>
        isVertEdge (d k) ∧ min ((pos d k).2) ((pos d (k + 1)).2) = m))
      = (Finset.univ.filter Pup) ∪ (Finset.univ.filter Pdown) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact hiff k
  have heq : (Finset.univ.filter Pup).card = (Finset.univ.filter Pdown).card := by
    simp only [hPup, hPdown]; exact upDown_card_eq d hclosed m
  rw [fullLineCross, hsplit, Finset.card_union_of_disjoint hdisj, heq]
  exact ⟨_, rfl⟩


end StatMech.Onsager.WalkCrossing
