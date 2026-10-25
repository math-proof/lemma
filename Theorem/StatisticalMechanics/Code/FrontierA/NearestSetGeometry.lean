/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FrontierA.NearestSetGeometry
open Set


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


theorem realizedL1Distances_nonempty {A B : Set (Site d)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (realizedL1Distances A B).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  exact ⟨l1dist d x y, x, hx, y, hy, rfl⟩


theorem exists_pair_setL1Distance {A B : Set (Site d)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x ∈ A, ∃ y ∈ B, l1dist d x y = setL1Distance A B := by
  have hmem := Nat.sInf_mem (realizedL1Distances_nonempty hA hB)
  simpa [setL1Distance, realizedL1Distances] using hmem


end StatMech.FrontierA
