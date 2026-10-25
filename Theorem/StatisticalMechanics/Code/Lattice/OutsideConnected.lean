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
import Def.StatisticalMechanics.Code.Lattice.OutsideConnected
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


@[simp] theorem oc_mem_supportSet (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) :
    z ∈ oc_supportSet Vc ↔ z ∈ Vc.support := Iff.rfl


theorem oc_offSupportLattice_reachable_iff (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∉ Vc.support) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y ↔
      ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support :=
  ffc_reachable_iff_offSupportWalk hx


theorem oc_exterior_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∉ Vc.support := by
  intro hzS
  have hzbox : z ∈ box 2 R := hsupp hzS
  rw [exterior_eq_compl_box] at hz
  exact hz hzbox


theorem oc_exterior_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∉ jec_leftRegion Vc :=
  egf_exterior_outside Vc R hsupp hz


theorem oc_exterior_adj_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) (hadj : (hypercubicLattice 2).Adj x y) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Adj x y :=
  ⟨hadj, oc_exterior_offSupport Vc R hsupp hx, oc_exterior_offSupport Vc R hsupp hy⟩


end Lattice
end StatMech
