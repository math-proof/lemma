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
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc15_facialOrbit_ne_of_component_ne (Vc : (hypercubicLattice 2).Walk a a)
    {s t : Site 2} (hs : s ∉ Vc.support)
    (hne : offSupportComponent Vc s ≠ offSupportComponent Vc t) :
    {e : Dart | IsBoundaryDart (offSupportComponent Vc s) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc t) e} := by
  have hdisj := rsf_disjoint_boundaryDarts_of_ne Vc hne
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hs
  intro heq
  have heU : e ∈ {d : Dart | IsBoundaryDart (offSupportComponent Vc s) d} := he
  have heV : e ∈ {d : Dart | IsBoundaryDart (offSupportComponent Vc t) d} := heq ▸ heU
  exact (Set.disjoint_left.mp hdisj) heU heV


theorem kc15_beacon_component_infinite (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)).Infinite := by
  set b : Site 2 := ![-((R : ℤ) + 1), 0] with hb
  have hbext : b ∈ exterior 2 R := kc12_farLeftBeacon_mem_exterior R
  have hboff : b ∉ Vc.support := by
    have := oc_exterior_offSupport Vc R hsupp hbext
    simpa [oc_supportSet] using this
  have hbmem : b ∈ (oc_supportSet Vc)ᶜ := kc13_mem_compl Vc hboff
  have hinf := kc4_extComponent_infinite Vc R hsupp hbext hbmem
  intro hfin
  have hfin' : (kc12_component Vc b).Finite := hfin
  exact hinf ((kc13_component_finite_iff Vc hboff hbmem).mpr hfin')


theorem kc15_beacon_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    (![-((R : ℤ) + 1), 0] : Site 2) ∉ Vc.support := by
  have := oc_exterior_offSupport Vc R hsupp (kc12_farLeftBeacon_mem_exterior R)
  simpa [oc_supportSet] using this


theorem kc15_beacon_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    (![-((R : ℤ) + 1), 0] : Site 2) ∉ jec_leftRegion Vc := by
  apply pww_farLeft_notMem_leftRegion
  intro p hp
  have hpbox : p ∈ box 2 R := hsupp (by simpa [oc_supportSet] using hp)
  rw [mem_box] at hpbox
  have h0 := hpbox 0
  change (![-((R : ℤ) + 1), 0] : Site 2) 0 ≤ p 0
  simp only [Matrix.cons_val_zero]
  omega


theorem kc15_finiteComponent_ne_beacon (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hfin : (offSupportComponent Vc z).Finite) :
    offSupportComponent Vc z ≠ offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2) := by
  intro heq
  have hinf := kc15_beacon_component_infinite Vc R hsupp
  rw [heq] at hfin
  exact hinf hfin


theorem kc15_outsideComponent_ne_insideComponent (Vc : (hypercubicLattice 2).Walk a a)
    {z x : Site 2} (hzout : z ∉ jec_leftRegion Vc) (hzoff : z ∉ Vc.support)
    (hxin : x ∈ jec_leftRegion Vc) :
    offSupportComponent Vc z ≠ offSupportComponent Vc x := by
  intro heq
  have hx : x ∈ offSupportComponent Vc x := seed_mem_offSupportComponent Vc x
  rw [← heq] at hx
  exact (offSupportComponent_subset_exterior Vc hzout hzoff hx) hxin


theorem kc15_secondBoundedRegion_third_facialOrbit (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z x : Site 2}
    (hzoff : z ∉ Vc.support) (hzout : z ∉ jec_leftRegion Vc)
    (hfin : (offSupportComponent Vc z).Finite)
    (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support) :
    {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ∧
    {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} ∧
    {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} := by
  refine ⟨?_, ?_, ?_⟩
  · exact kc15_facialOrbit_ne_of_component_ne Vc hzoff
      (kc15_outsideComponent_ne_insideComponent Vc hzout hzoff hxin)
  · exact kc15_facialOrbit_ne_of_component_ne Vc hzoff
      (kc15_finiteComponent_ne_beacon Vc R hsupp hfin)
  · refine kc15_facialOrbit_ne_of_component_ne Vc hxoff ?_
    
    refine fun heq => (kc15_outsideComponent_ne_insideComponent Vc
      (kc15_beacon_outside Vc R hsupp) (kc15_beacon_offSupport Vc R hsupp) hxin) heq.symm


end Walls
end StatMech
