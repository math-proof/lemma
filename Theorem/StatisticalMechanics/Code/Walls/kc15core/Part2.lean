/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc14core.Part2
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FacialSurjectivity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FacialSurjectivityProve
import Def.StatisticalMechanics.Code.Walls.kc15core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc15_facialOrbit_mem_family (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {x z : Site 2}
    (hz : z ∉ Vc.support) (hres : kc15_FacialOrbitFamilyTwo Vc R x) :
    {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} =
        {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ∨
      {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} =
        {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} := by
  have hmem : {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e}
      ∈ Set.range (rsf_componentDarts Vc) :=
    ⟨(fcb_offComplGraph Vc).connectedComponentMk ⟨z, hz⟩, rsf_componentDarts_mk Vc ⟨z, hz⟩⟩
  unfold kc15_FacialOrbitFamilyTwo rsf_FacialOrbitsCoverComponents at hres
  rw [hres] at hmem
  simpa only [kc15_facialFamily, Set.mem_insert_iff, Set.mem_singleton_iff] using hmem


theorem kc15_noSecondBoundedRegion_of_facialOrbitFamilyTwo (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R) {x : Site 2}
    (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hres : kc15_FacialOrbitFamilyTwo Vc R x) :
    kc14_NoSecondBoundedRegion Vc := by
  intro z hzoff hzout hfin
  obtain ⟨hzx, hzb, _⟩ :=
    kc15_secondBoundedRegion_third_facialOrbit Vc R hsupp hzoff hzout hfin hxin hxoff
  rcases kc15_facialOrbit_mem_family Vc R hzoff hres with h | h
  · exact hzx h
  · exact hzb h


theorem kc15_offSupportOutsideInfinite_of_facialOrbitFamilyTwo (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a) {x : Site 2}
    (hxin : x ∈ jec_leftRegion (mpl_orbitLoop K a)) (hxoff : x ∉ (mpl_orbitLoop K a).support)
    (hres : kc15_FacialOrbitFamilyTwo (mpl_orbitLoop K a) R x) :
    kc7_OffSupportOutsideInfinite K a :=
  kc14_offSupportOutsideInfinite_of_noSecondBoundedRegion K a R hRbox hbridge
    (kc15_noSecondBoundedRegion_of_facialOrbitFamilyTwo (mpl_orbitLoop K a) R hRbox hxin hxoff hres)


end Walls
end StatMech
