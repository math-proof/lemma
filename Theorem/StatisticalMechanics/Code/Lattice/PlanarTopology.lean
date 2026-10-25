/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.PlanarTopology
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem nearestNeighbour_iff_shift (d : ℕ) (x y : Site d) :
    NearestNeighbour d x y ↔ ∃ j : Fin d, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ y = shift d x j s := by
  constructor
  · intro h
    unfold NearestNeighbour at h
    
    have hne : ∃ j, (x j - y j).natAbs ≠ 0 := by
      by_contra hc
      push Not at hc
      simp only [hc] at h
      simp at h
    obtain ⟨j, hj⟩ := hne
    
    have hle : (x j - y j).natAbs ≤ ∑ i, (x i - y i).natAbs :=
      Finset.single_le_sum (f := fun i => (x i - y i).natAbs)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [h] at hle
    have h1 : (x j - y j).natAbs = 1 := by omega
    
    have hother : ∀ i, i ≠ j → (x i - y i).natAbs = 0 := by
      intro i hi
      by_contra hc
      have hpair : (x j - y j).natAbs + (x i - y i).natAbs ≤ ∑ k, (x k - y k).natAbs := by
        have := Finset.sum_le_sum_of_subset (s := ({j, i} : Finset (Fin d))) (t := Finset.univ)
          (f := fun k => (x k - y k).natAbs) (Finset.subset_univ _)
        rwa [Finset.sum_pair (Ne.symm hi)] at this
      rw [h] at hpair; omega
    refine ⟨j, y j - x j, ?_, ?_⟩
    · rcases Int.natAbs_eq (x j - y j) with he | he <;> rw [h1] at he <;> omega
    · funext i
      by_cases hi : i = j
      · subst hi; simp [shift, Function.update_self]
      · rw [shift, Function.update_of_ne hi]; have := hother i hi; omega
  · rintro ⟨j, s, hs, rfl⟩
    unfold NearestNeighbour shift
    rw [Finset.sum_eq_single j]
    · rw [Function.update_self]
      rcases hs with rfl | rfl <;> simp
    · intro i _ hi; rw [Function.update_of_ne hi]; simp
    · intro h; simp at h


theorem adj_candMap (d : ℕ) (x : Site d) (p : Fin d × Bool) :
    (hypercubicLattice d).Adj x (candMap d x p) := by
  change NearestNeighbour d x (candMap d x p)
  rw [nearestNeighbour_iff_shift]
  exact ⟨p.1, if p.2 then 1 else -1, by rcases p.2 <;> simp, rfl⟩


theorem mem_candFinset_of_adj (d : ℕ) (x y : Site d)
    (h : (hypercubicLattice d).Adj x y) : y ∈ candFinset d x := by
  change NearestNeighbour d x y at h
  rw [nearestNeighbour_iff_shift] at h
  obtain ⟨j, s, hs, hys⟩ := h
  rw [candFinset, Finset.mem_image]
  refine ⟨(j, s = 1), Finset.mem_univ _, ?_⟩
  rw [candMap]
  rcases hs with rfl | rfl
  · simp [hys]
  · simp [hys, shift]


theorem candMap_injective (d : ℕ) (x : Site d) : Function.Injective (candMap d x) := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  simp only [candMap, shift] at h
  by_cases hjj : j = j'
  · subst hjj
    have := congrFun h j
    rw [Function.update_self, Function.update_self] at this
    rcases b <;> rcases b' <;> simp_all
  · have hj := congrFun h j
    rw [Function.update_self, Function.update_of_ne hjj] at hj
    rcases b <;> simp_all


end Lattice
end StatMech
