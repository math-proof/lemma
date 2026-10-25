/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open Set Finset


namespace StatMech

namespace Lattice

@[simp]
theorem mem_edgeBoundary {d : ℕ} {S : Set (Site d)} {x y : Site d} :
    (x, y) ∈ edgeBoundary d S ↔ (hypercubicLattice d).Adj x y ∧ (x ∈ S ↔ y ∉ S) :=
  Iff.rfl


theorem edgeBoundary_symm {d : ℕ} {S : Set (Site d)} {x y : Site d}
    (h : (x, y) ∈ edgeBoundary d S) : (y, x) ∈ edgeBoundary d S := by
  obtain ⟨hadj, hxy⟩ := h
  refine ⟨(hypercubicLattice d).symm.symm _ _ hadj, ?_⟩
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> tauto


theorem box_mono (d : ℕ) : Monotone (box d) := by
  intro m n hmn x hx i
  exact le_trans (hx i) hmn

theorem box_subset_succ (d n : ℕ) : box d n ⊆ box d (n + 1) :=
  box_mono d (Nat.le_succ n)


theorem iUnion_box (d : ℕ) : (⋃ n, box d n) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  refine ⟨Finset.univ.sup (fun i => (x i).natAbs), fun i => ?_⟩
  exact Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)

end Lattice
end StatMech
