/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.Lattice.OutsideConnected.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem oc_exterior_reachable_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
  have hmap := (box_exterior_connected R (by norm_num) x y hx hy).map
    (oc_extToOffSupportHom Vc R hsupp)
  simpa [oc_extToOffSupportHom] using hmap


theorem oc_farExterior_offSupport_walk (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support :=
  (oc_offSupportLattice_reachable_iff Vc (oc_exterior_offSupport Vc R hsupp hx)).mp
    (oc_exterior_reachable_offSupport Vc R hsupp hx hy)


end Lattice
end StatMech
