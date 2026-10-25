/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem arcxc_exterior_offSupport {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R) {z : Site 2}
    (hz : z ∈ exterior 2 R) : z ∉ B := by
  intro hzB
  rw [exterior_eq_compl_box] at hz
  exact hz (hB hzB)


theorem arcxc_exterior_adj_offSupport {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) (hadj : (hypercubicLattice 2).Adj x y) :
    (ffc_offSupportLattice B).Adj x y :=
  ⟨hadj, arcxc_exterior_offSupport hB hx, arcxc_exterior_offSupport hB hy⟩


end Lattice
end StatMech
