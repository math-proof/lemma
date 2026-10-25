/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
import Def.StatisticalMechanics.Code.Lattice.FacialSurjectivity.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem fsv_RegionSingleFace_singleton (c : Site 2) :
    fsv_RegionSingleFace ({c} : Set (Site 2)) :=
  fun e he => fsv_boundaryDartSet_eq_orbit ({c} : Set (Site 2)) he
    (fun d hd => ifc_singleton_sameOrbit c e d he hd)


theorem fsv_canonical_eq_singleOrbit {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
    fsv_canonicalFamily Vc = fsv_singleOrbitFamily Vc := by
  ext D
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hz
    exact ⟨z, hz, e, he, hres z hz e he⟩
  · rintro ⟨z, hz, e, he, rfl⟩
    exact ⟨z, hz, (hres z hz e he).symm⟩


theorem fsv_facialOrbitsCoverComponents_singleOrbit {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
    rsf_FacialOrbitsCoverComponents Vc (fsv_singleOrbitFamily Vc) := by
  unfold rsf_FacialOrbitsCoverComponents
  rw [fsv_range_eq_canonical, fsv_canonical_eq_singleOrbit Vc hres]


theorem fsv_componentCount_eq_singleOrbitCount {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent
      = Nat.card (fsv_singleOrbitFamily Vc) :=
  rsf_componentCount_eq_facialOrbitCount Vc (fsv_facialOrbitsCoverComponents_singleOrbit Vc hres)

end Lattice
end StatMech
