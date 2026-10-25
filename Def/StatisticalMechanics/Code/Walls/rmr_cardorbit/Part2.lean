/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rmr_cardorbit
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


noncomputable def boxOrbitEquivSlabBox (A B : Set (ConfigSpace α))
    (k : ConfigSpace α × ConfigSpace α) :
    {p // p ∈ boxOrbit A B k} ≃ {ω // ω ∈ slabBox A B k} where
  toFun p := ⟨p.1.1, by
    obtain ⟨hbox, hk⟩ := mem_boxOrbit.mp p.2
    rw [mem_slabBox]
    refine ⟨hbox, ?_⟩
    rw [← pair_eq_of_orbitKey hk]; exact hk⟩
  invFun ω := ⟨(ω.1, poc_keyFlip k ω.1), by
    obtain ⟨hbox, hk⟩ := mem_slabBox.mp ω.2
    rw [mem_boxOrbit]; exact ⟨hbox, hk⟩⟩
  left_inv p := by
    obtain ⟨_, hk⟩ := mem_boxOrbit.mp p.2
    exact Subtype.ext (pair_eq_of_orbitKey hk).symm
  right_inv ω := rfl


noncomputable def imgOrbitEquivSlabImg (A B : Set (ConfigSpace α))
    (k : ConfigSpace α × ConfigSpace α) :
    {q // q ∈ imgOrbit A B k} ≃ {ω // ω ∈ slabImg A B k} where
  toFun q := ⟨q.1.1, by
    obtain ⟨hA, hB, hk⟩ := mem_imgOrbit.mp q.2
    rw [mem_slabImg]
    refine ⟨hA, ?_, ?_⟩
    · rw [← poc_snd_eq q.1 k hk]; exact hB
    · rw [← pair_eq_of_orbitKey hk]; exact hk⟩
  invFun ω := ⟨(ω.1, poc_keyFlip k ω.1), by
    obtain ⟨hA, hB, hk⟩ := mem_slabImg.mp ω.2
    rw [mem_imgOrbit]; exact ⟨hA, hB, hk⟩⟩
  left_inv q := by
    obtain ⟨_, _, hk⟩ := mem_imgOrbit.mp q.2
    exact Subtype.ext (pair_eq_of_orbitKey hk).symm
  right_inv ω := rfl


end StatMech.Walls
