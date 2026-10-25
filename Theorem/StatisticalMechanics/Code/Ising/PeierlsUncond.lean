/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Def.StatisticalMechanics.Code.Ising.PeierlsUncond
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


@[simp] lemma flipOnSet_apply (K : Set (Site d)) (σ : ConfigSpace (Site d)) (x : Site d) :
    flipOnSet K σ x = if x ∈ K then !(σ x) else σ x := rfl

lemma flipOnSet_mem (K : Set (Site d)) (σ : ConfigSpace (Site d)) {x : Site d} (hx : x ∈ K) :
    flipOnSet K σ x = !(σ x) := by rw [flipOnSet_apply, if_pos hx]

lemma flipOnSet_not_mem (K : Set (Site d)) (σ : ConfigSpace (Site d)) {x : Site d}
    (hx : x ∉ K) : flipOnSet K σ x = σ x := by rw [flipOnSet_apply, if_neg hx]


lemma spin_flipOnSet_mem (K : Set (Site d)) (σ : ConfigSpace (Site d)) {x : Site d}
    (hx : x ∈ K) : spin (flipOnSet K σ) x = - spin σ x := by
  unfold spin; rw [flipOnSet_mem K σ hx]; by_cases h : σ x <;> simp [h]


lemma spin_flipOnSet_not_mem (K : Set (Site d)) (σ : ConfigSpace (Site d)) {x : Site d}
    (hx : x ∉ K) : spin (flipOnSet K σ) x = spin σ x := by
  unfold spin; rw [flipOnSet_not_mem K σ hx]


end Ising
end StatMech
