/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part8


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_portEdge_rev (L : ℕ) (d : ons_Dart L) :
    ons_portEdge L (ons_dartRev L d) = ons_portEdge L d := by
  rcases d with ⟨s, mu⟩
  simp only [ons_portEdge, ons_dartRev]
  rw [ons_dirStep_opposite]
  exact Sym2.eq_swap

theorem ons_torus_neighborFinset_steps (L : ℕ) [Fact (2 < L)]
    (v : ZMod L × ZMod L) :
    (onsTorusGraph L).neighborFinset v =
      {ons_dirStep L 0 v, ons_dirStep L 1 v,
        ons_dirStep L 2 v, ons_dirStep L 3 v} := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases v with ⟨vx, vy⟩
  rcases w with ⟨wx, wy⟩
  simp only [onsTorusGraph, onsTorusAdj]
  constructor
  · rintro (⟨hx, hy | hy⟩ | ⟨hy, hx | hx⟩)
    · right; right; right
      apply Prod.ext <;> simp [ons_dirStep, hx] <;> linear_combination -hy
    · right; left
      apply Prod.ext <;> simp [ons_dirStep, hx] <;> linear_combination -hy
    · right; right; left
      apply Prod.ext <;> simp [ons_dirStep, hy] <;> linear_combination -hx
    · left
      apply Prod.ext <;> simp [ons_dirStep, hy] <;> linear_combination -hx
  · rintro (h | h | h | h)
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [ons_dirStep] at hx hy
      exact Or.inr ⟨hy.symm, Or.inr (by linear_combination -hx)⟩
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [ons_dirStep] at hx hy
      exact Or.inl ⟨hx.symm, Or.inr (by linear_combination -hy)⟩
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [ons_dirStep] at hx hy
      exact Or.inr ⟨hy.symm, Or.inl (by linear_combination -hx)⟩
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [ons_dirStep] at hx hy
      exact Or.inl ⟨hx.symm, Or.inl (by linear_combination -hy)⟩

theorem ons_dirStep_injective (L : ℕ) [Fact (2 < L)]
    (v : ZMod L × ZMod L) :
    Function.Injective (fun mu : Fin 4 => ons_dirStep L mu v) := by
  haveI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  have h2 : (2 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    have := (Fact.out : 2 < L)
    omega
  intro mu nu h
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_dirStep, Prod.ext_iff, h1] at h ⊢ <;>
    try {exfalso; apply h2; linear_combination h} <;>
    try {exfalso; apply h2; linear_combination -h}

theorem ons_torus_neighbor_sum_eq_direction_sum (L : ℕ) [Fact (2 < L)]
    (v : ZMod L × ZMod L) (f : (ZMod L × ZMod L) → ZMod 2) :
    ∑ w ∈ (onsTorusGraph L).neighborFinset v, f w =
      ∑ mu : Fin 4, f (ons_dirStep L mu v) := by
  rw [ons_torus_neighborFinset_steps]
  have hset : ({ons_dirStep L 0 v, ons_dirStep L 1 v,
      ons_dirStep L 2 v, ons_dirStep L 3 v} : Finset (ZMod L × ZMod L)) =
      Finset.univ.image (fun mu : Fin 4 => ons_dirStep L mu v) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨mu, rfl⟩
      fin_cases mu <;> simp
  rw [hset, Finset.sum_image (fun _ _ _ _ h => ons_dirStep_injective L v h)]

end StatMech.Onsager
