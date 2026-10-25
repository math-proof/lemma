/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part2
open Set


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


theorem nearestSourceSet_subset (A B : Set (Site d)) :
    nearestSourceSet A B ⊆ A := fun _ hx => hx.1


theorem nearestSourceSet_nonempty {A B : Set (Site d)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (nearestSourceSet A B).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_pair_setL1Distance hA hB
  exact ⟨x, hx, y, hy, hxy⟩


theorem mem_nearestSourceSet_iff {A B : Set (Site d)} {x : Site d} :
    x ∈ nearestSourceSet A B ↔
      x ∈ A ∧ ∃ y ∈ B, ∀ x' ∈ A, ∀ y' ∈ B,
        l1dist d x y ≤ l1dist d x' y' := by
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    refine ⟨hx, y, hy, ?_⟩
    intro x' hx' y' hy'
    rw [hxy]
    exact Nat.sInf_le ⟨x', hx', y', hy', rfl⟩
  · rintro ⟨hx, y, hy, hmin⟩
    have hnonempty : (realizedL1Distances A B).Nonempty :=
      ⟨l1dist d x y, x, hx, y, hy, rfl⟩
    obtain ⟨u, hu, v, hv, huv⟩ :=
      (show setL1Distance A B ∈ realizedL1Distances A B by
        exact Nat.sInf_mem hnonempty)
    refine ⟨hx, y, hy, le_antisymm ?_ ?_⟩
    · exact hmin u hu v hv |>.trans_eq huv
    · exact Nat.sInf_le ⟨x, hx, y, hy, rfl⟩


end StatMech.FrontierA
