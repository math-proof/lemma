/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.BeffaraDC.AnimalLLN


namespace StatMech

namespace BeffaraDC

open Finset Filter Topology

open scoped Topology

variable {V : Type*} [DecidableEq V] [Fintype V]


lemma mem_animalsLE {o : V} {n : ℕ} {S : Finset V} :
    S ∈ animalsLE o n ↔ o ∈ S ∧ S.card ≤ n := by
  simp [animalsLE]


lemma animalsLE_nonempty (o : V) {n : ℕ} (hn : 1 ≤ n) : (animalsLE o n).Nonempty :=
  ⟨{o}, by rw [mem_animalsLE]; exact ⟨mem_singleton_self o, by simpa using hn⟩⟩


lemma animalsLE_mono (o : V) {m n : ℕ} (h : m ≤ n) : animalsLE o m ⊆ animalsLE o n := by
  intro S hS
  rw [mem_animalsLE] at hS ⊢
  exact ⟨hS.1, hS.2.trans h⟩


end BeffaraDC
end StatMech
