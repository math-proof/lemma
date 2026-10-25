/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_mem_firstWitness_iff {N : ℕ} {W : Fin N → Set (ConfigSpace E)}
    {i : Fin N} {omega : ConfigSpace E} :
    omega ∈ rlc_firstWitness W i ↔
      omega ∈ W i ∧ ∀ j : Fin N, j < i → omega ∉ W j := by
  simp [rlc_firstWitness]


theorem rlc_firstWitness_pairwiseDisjoint {N : ℕ}
    (W : Fin N → Set (ConfigSpace E)) :
    Pairwise (Disjoint on rlc_firstWitness W) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · change Disjoint (rlc_firstWitness W i) (rlc_firstWitness W j)
    rw [Set.disjoint_left]
    intro omega hi hj
    exact (rlc_mem_firstWitness_iff.mp hj).2 i hij'
      (rlc_mem_firstWitness_iff.mp hi).1
  · change Disjoint (rlc_firstWitness W i) (rlc_firstWitness W j)
    rw [Set.disjoint_left]
    intro omega hi hj
    exact (rlc_mem_firstWitness_iff.mp hi).2 j hji'
      (rlc_mem_firstWitness_iff.mp hj).1


theorem rlc_iUnion_firstWitness {N : ℕ} (W : Fin N → Set (ConfigSpace E)) :
    (⋃ i, rlc_firstWitness W i) = ⋃ i, W i := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono fun i => diff_subset
  · intro omega homega
    simp only [Set.mem_iUnion] at homega ⊢
    obtain ⟨i, hi⟩ := homega
    let P : ℕ → Prop := fun k => ∃ hk : k < N, omega ∈ W ⟨k, hk⟩
    have hP : ∃ k, P k := ⟨i, i.isLt, hi⟩
    let k := Nat.find hP
    have hk : P k := Nat.find_spec hP
    refine ⟨⟨k, hk.1⟩, rlc_mem_firstWitness_iff.mpr ⟨hk.2, ?_⟩⟩
    intro j hji hj
    have hmin : k ≤ j := Nat.find_min' hP ⟨j.isLt, hj⟩
    exact (not_le_of_gt hji) hmin


end Universality
end StatMech
