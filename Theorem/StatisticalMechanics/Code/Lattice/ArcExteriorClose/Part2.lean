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
import Def.StatisticalMechanics.Code.Lattice.ArcExteriorClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem arcxc_exterior_reachable_offSupport {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (ffc_offSupportLattice B).Reachable x y := by
  have hmap := (box_exterior_connected R (by norm_num) x y hx hy).map (arcxc_extToOffSupportHom hB)
  simpa [arcxc_extToOffSupportHom] using hmap


theorem arcxc_exterior_walk_offSupport {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B :=
  (ffc_reachable_iff_offSupportWalk (arcxc_exterior_offSupport hB hx)).mp
    (arcxc_exterior_reachable_offSupport hB hx hy)


end Lattice
end StatMech
