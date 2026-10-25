/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open Set Finset


namespace StatMech

namespace Lattice

open StatMech.Ising

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem ccb_adj_mem_box_succ {n : ℕ} {x y : Site d} (h : (hypercubicLattice d).Adj x y)
    (hx : x ∈ box d n) : y ∈ box d (n + 1) := by
  rw [mem_box]; intro i
  have h1 : (x i - y i).natAbs ≤ 1 := by
    rw [hypercubicLattice_adj] at h
    calc (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
          Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
            (by intros; positivity) (Finset.mem_univ i)
      _ = 1 := h
  have h2 : (x i).natAbs ≤ n := hx i
  omega


theorem ccb_boundary_step_mem_crossEdges {K : Finset (Site d)} {n : ℕ} {a b : Site d}
    (hadj : (hypercubicLattice d).Adj a b) (haK : a ∈ K) (hbK : b ∉ K) (hab : a ∈ box d n) :
    s(a, b) ∈ crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n) := by
  rw [crossEdges, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [bondFinsetTouch, Finset.mem_image]
    refine ⟨(a, b), ?_, rfl⟩
    rw [bondPairsTouch, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hadj, Or.inl hab⟩
    · rw [mem_boxFinset]; exact box_subset_succ d n hab
    · rw [mem_boxFinset]; exact ccb_adj_mem_box_succ hadj hab
  · rw [crosses_mk]; exact ⟨fun _ => hbK, fun _ => haK⟩


end Lattice
end StatMech
