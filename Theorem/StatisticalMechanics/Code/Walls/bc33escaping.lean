/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc30armforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc31globalarm.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc32forestsep.Part2
import Def.StatisticalMechanics.Code.Walls.bc33escaping
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc33_rayWalk_support {V : Type*} (G : SimpleGraph V) (r : ℕ → V)
    (hadj : ∀ k, G.Adj (r k) (r (k + 1))) (j : ℕ) :
    ∀ v ∈ (bc33_rayWalk G r hadj j).support, ∃ k ≤ j, v = r k := by
  induction j with
  | zero =>
    intro v hv
    rw [bc33_rayWalk, Walk.support_nil, List.mem_singleton] at hv
    exact ⟨0, le_refl _, hv⟩
  | succ i ih =>
    intro v hv
    rw [bc33_rayWalk, Walk.support_concat, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | hv
    · obtain ⟨k, hk, rfl⟩ := ih v hv
      exact ⟨k, by omega, rfl⟩
    · exact ⟨i+1, le_refl _, hv⟩


theorem bc33_injRay_escapes_box (r : ℕ → Site d) (hinj : Function.Injective r) (m : ℕ) :
    ∃ j, r j ∉ box d m := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hsub : Set.range r ⊆ box d m := by rintro x ⟨j, rfl⟩; exact h j
  have hrangefin : (Set.range r).Finite := (box_finite d m).subset hsub
  exact (Set.infinite_range_of_injective hinj) hrangefin


theorem bc33_escapingWalks_of_TavoidingRay (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a : Site d} (r : ℕ → Site d) (hr0 : r 0 = a)
    (hinj : Function.Injective r)
    (hadj : ∀ k, (openSubgraph d (removeSite x ω)).Adj (r k) (r (k + 1)))
    (hT : ∀ k, r k ∉ tfc_trifFinset ω n) :
    ∀ m : ℕ, ∃ z, z ∉ box d m ∧
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z,
        ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n := by
  intro m
  obtain ⟨j, hj⟩ := bc33_injRay_escapes_box r hinj m
  subst hr0
  refine ⟨r j, hj, bc33_rayWalk _ r hadj j, ?_⟩
  intro v hv
  obtain ⟨k, _hk, rfl⟩ := bc33_rayWalk_support _ r hadj j v hv
  exact hT k


end StatMech.Walls
