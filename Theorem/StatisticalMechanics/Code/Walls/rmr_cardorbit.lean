/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Def.StatisticalMechanics.Code.Walls.rmr_cardorbit
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


@[simp] theorem slabBox_def (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    slabBox A B k = poc_slabBox A B k := rfl

@[simp] theorem slabImg_def (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    slabImg A B k = poc_slabImg A B k := rfl


theorem mem_slabBox {A B : Set (ConfigSpace α)} {k : ConfigSpace α × ConfigSpace α}
    {ω : ConfigSpace α} :
    ω ∈ slabBox A B k ↔
      ω ∈ disjointOccurrence A B ∧ orbitKey (ω, poc_keyFlip k ω) = k := by
  simp only [slabBox, poc_slabBox, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_slabImg {A B : Set (ConfigSpace α)} {k : ConfigSpace α × ConfigSpace α}
    {ω : ConfigSpace α} :
    ω ∈ slabImg A B k ↔
      ω ∈ A ∧ poc_keyFlip k ω ∈ B ∧ orbitKey (ω, poc_keyFlip k ω) = k := by
  simp only [slabImg, poc_slabImg, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_boxOrbit {A B : Set (ConfigSpace α)} {k : ConfigSpace α × ConfigSpace α}
    {p : ConfigSpace α × ConfigSpace α} :
    p ∈ boxOrbit A B k ↔ p.1 ∈ disjointOccurrence A B ∧ orbitKey p = k := by
  simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_imgOrbit {A B : Set (ConfigSpace α)} {k : ConfigSpace α × ConfigSpace α}
    {q : ConfigSpace α × ConfigSpace α} :
    q ∈ imgOrbit A B k ↔ q.1 ∈ A ∧ q.2 ∈ B ∧ orbitKey q = k := by
  simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and]


omit [Fintype α] [DecidableEq α] in


theorem pair_eq_of_orbitKey {p : ConfigSpace α × ConfigSpace α}
    {k : ConfigSpace α × ConfigSpace α} (hk : orbitKey p = k) :
    p = (p.1, poc_keyFlip k p.1) :=
  Prod.ext rfl (poc_snd_eq p k hk)


end StatMech.Walls
