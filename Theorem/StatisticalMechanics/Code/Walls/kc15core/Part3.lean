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
import Def.StatisticalMechanics.Code.Walls.kc15core.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc15_noSecondBoundedRegion_of_outsideOneFacialOrbit (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hres : kc15_OutsideOneFacialOrbit Vc R) :
    kc14_NoSecondBoundedRegion Vc := by
  intro z hzoff hzout hfin
  have hne : {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} :=
    kc15_facialOrbit_ne_of_component_ne Vc hzoff (kc15_finiteComponent_ne_beacon Vc R hsupp hfin)
  exact hne (hres z hzoff hzout)


theorem kc15_outsideOneFacialOrbit_of_reachesFarLeftBeacon (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hres : kc12_ReachesFarLeftBeacon Vc R) :
    kc15_OutsideOneFacialOrbit Vc R := by
  intro z hzoff hzout
  obtain ⟨p, hp⟩ := hres z hzoff hzout
  have hr : (offSupport Vc).Reachable z (![-((R : ℤ) + 1), 0] : Site 2) :=
    offSupportWalk_to_offSupport_reachable Vc p hp
  have hcomp : offSupportComponent Vc z
      = offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2) := by
    ext w; rw [mem_offSupportComponent, mem_offSupportComponent]
    exact ⟨fun h => hr.symm.trans h, fun h => hr.trans h⟩
  rw [hcomp]


theorem kc15_facialOrbitFamilyTwo_of_sides (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x : Site 2}
    (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ w ∈ p.support, w ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ w ∈ p.support, w ∉ Vc.support) :
    kc15_FacialOrbitFamilyTwo Vc R x := by
  unfold kc15_FacialOrbitFamilyTwo rsf_FacialOrbitsCoverComponents kc15_facialFamily
  rw [fsv_range_eq_canonical]
  exact fsp_canonicalFamily_eq_pair Vc hxin hxoff (kc15_beacon_outside Vc R hsupp)
    (kc15_beacon_offSupport Vc R hsupp) hin hout


theorem kc15_unitCell_outsideOneFacialOrbit :
    kc15_OutsideOneFacialOrbit (mpl_orbitLoop unitCell ucBase) 1 :=
  kc15_outsideOneFacialOrbit_of_reachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1
    kc12_unitCell_reachesFarLeftBeacon


theorem kc15_unitCell_noSecondBoundedRegion_via_facialOrbit :
    kc14_NoSecondBoundedRegion (mpl_orbitLoop unitCell ucBase) :=
  kc15_noSecondBoundedRegion_of_outsideOneFacialOrbit (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc15_unitCell_outsideOneFacialOrbit


theorem kc15_unitCell_finiteComponent_facialOrbit_ne (z : Site 2)
    (hzoff : z ∉ (mpl_orbitLoop unitCell ucBase).support)
    (hfin : (offSupportComponent (mpl_orbitLoop unitCell ucBase) z).Finite) :
    {e : Dart | IsBoundaryDart (offSupportComponent (mpl_orbitLoop unitCell ucBase) z) e} ≠
      {e : Dart | IsBoundaryDart
        (offSupportComponent (mpl_orbitLoop unitCell ucBase) (![-((1 : ℤ) + 1), 0] : Site 2)) e} :=
  kc15_facialOrbit_ne_of_component_ne (mpl_orbitLoop unitCell ucBase) hzoff
    (kc15_finiteComponent_ne_beacon (mpl_orbitLoop unitCell ucBase) 1 kc8_unitCell_supp_box hfin)

end Walls
end StatMech
