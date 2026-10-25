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
import Def.StatisticalMechanics.Code.Lattice.FacialSurjectivity
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem fsv_range_eq_canonical {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Set.range (rsf_componentDarts Vc) = fsv_canonicalFamily Vc := by
  ext D
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := c.exists_rep
    exact ⟨v.1, v.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(fcb_offComplGraph Vc).connectedComponentMk ⟨z, hz⟩, rfl⟩


theorem fsv_facialOrbitsCoverComponents_canonical {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    rsf_FacialOrbitsCoverComponents Vc (fsv_canonicalFamily Vc) :=
  fsv_range_eq_canonical Vc


theorem fsv_componentCount_eq_canonicalCount {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent
      = Nat.card (fsv_canonicalFamily Vc) :=
  rsf_componentCount_eq_facialOrbitCount Vc (fsv_facialOrbitsCoverComponents_canonical Vc)


theorem fsv_boundaryDartSet_dartNext_closed (C : Set (Site 2)) {e : Dart}
    (he : IsBoundaryDart C e) : IsBoundaryDart C (dartNext C e) :=
  dartNext_isBoundaryDart C e he


theorem fsv_orbit_subset_boundaryDartSet (C : Set (Site 2)) {e : Dart}
    (he : IsBoundaryDart C e) :
    {d : Dart | SameOrbit C e d} ⊆ {d : Dart | IsBoundaryDart C d} := by
  rintro d ⟨n, rfl⟩
  exact rsf_orbit_isBoundaryDart C he n


theorem fsv_canonicalFamily_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {D : Set Dart} (hD : D ∈ fsv_canonicalFamily Vc) : D.Nonempty := by
  obtain ⟨z, hz, rfl⟩ := hD
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hz
  exact ⟨e, he⟩


theorem fsv_boundaryDartSet_eq_orbit (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e)
    (hsat : ∀ d : Dart, IsBoundaryDart C d → SameOrbit C e d) :
    {d : Dart | IsBoundaryDart C d} = {d : Dart | SameOrbit C e d} := by
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hd; exact hsat d hd
  · rintro ⟨n, rfl⟩; exact rsf_orbit_isBoundaryDart C he n


theorem fsv_hsat_of_interfaceConnected (C : Set (Site 2)) (hIC : InterfaceConnected C)
    {e : Dart} (he : IsBoundaryDart C e)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart C d) →
      ((hypercubicLattice 2).induce Cᶜ).Reachable ⟨e.head, he.2⟩ ⟨d.head, hd.2⟩) :
    ∀ d : Dart, IsBoundaryDart C d → SameOrbit C e d :=
  fun d hd => hIC e d he hd (hheads d hd)


theorem fsv_canonicalMember_eq_orbit_of_residues {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hIC : InterfaceConnected (offSupportComponent Vc z))
    {e : Dart} (he : IsBoundaryDart (offSupportComponent Vc z) e)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart (offSupportComponent Vc z) d) →
      ((hypercubicLattice 2).induce (offSupportComponent Vc z)ᶜ).Reachable
        ⟨e.head, he.2⟩ ⟨d.head, hd.2⟩) :
    {d : Dart | IsBoundaryDart (offSupportComponent Vc z) d}
      = {d : Dart | SameOrbit (offSupportComponent Vc z) e d} :=
  fsv_boundaryDartSet_eq_orbit (offSupportComponent Vc z) he
    (fsv_hsat_of_interfaceConnected (offSupportComponent Vc z) hIC he hheads)


end Lattice
end StatMech
