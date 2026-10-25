/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Def.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rsf_componentCount_eq_facialOrbitCount {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {𝓕 : Set (Set Dart)} (hcov : rsf_FacialOrbitsCoverComponents Vc 𝓕) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = Nat.card 𝓕 := by
  rw [rsf_componentCount_le_facialOrbitRange Vc]
  unfold rsf_FacialOrbitsCoverComponents at hcov
  rw [hcov]


theorem rsf_componentDarts_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c : (fcb_offComplGraph Vc).ConnectedComponent) :
    (rsf_componentDarts Vc c).Nonempty := by
  refine ConnectedComponent.ind ?_ c
  intro v
  rw [rsf_componentDarts_mk]
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc v.2
  exact ⟨e, he⟩


theorem rsf_facialOrbitRange_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : z ∉ Vc.support) :
    (Set.range (rsf_componentDarts Vc)).Nonempty :=
  ⟨rsf_componentDarts Vc ((fcb_offComplGraph Vc).connectedComponentMk ⟨z, hz⟩),
    Set.mem_range_self _⟩

end Lattice
end StatMech
