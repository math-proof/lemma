/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc13core
import Def.StatisticalMechanics.Code.Walls.kc14core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc14_noFiniteHole_of_noSecondBoundedRegion (Vc : (hypercubicLattice 2).Walk a a)
    (hres : kc14_NoSecondBoundedRegion Vc) : kc13_NoFiniteHole Vc := by
  intro z hzoff hzout hzmem hfin
  have hgeomfin : (kc12_component Vc z).Finite :=
    (kc13_component_finite_iff Vc hzoff hzmem).mp hfin
  exact hres z hzoff hzout hgeomfin


theorem kc14_noSecondBoundedRegion_of_noFiniteHole (Vc : (hypercubicLattice 2).Walk a a)
    (hres : kc13_NoFiniteHole Vc) : kc14_NoSecondBoundedRegion Vc := by
  intro z hzoff hzout hgeomfin
  have hzmem : z ∈ (oc_supportSet Vc)ᶜ := kc13_mem_compl Vc hzoff
  exact hres z hzoff hzout hzmem ((kc13_component_finite_iff Vc hzoff hzmem).mpr hgeomfin)


theorem kc14_noSecondBoundedRegion_iff_noFiniteHole (Vc : (hypercubicLattice 2).Walk a a) :
    kc14_NoSecondBoundedRegion Vc ↔ kc13_NoFiniteHole Vc :=
  ⟨kc14_noFiniteHole_of_noSecondBoundedRegion Vc,
   kc14_noSecondBoundedRegion_of_noFiniteHole Vc⟩


theorem kc14_reachesFarLeftBeacon_of_noSecondBoundedRegion (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R) (hres : kc14_NoSecondBoundedRegion Vc) :
    kc12_ReachesFarLeftBeacon Vc R :=
  kc13_reachesFarLeftBeacon_of_noFiniteHole Vc R hsupp
    (kc14_noFiniteHole_of_noSecondBoundedRegion Vc hres)


theorem kc14_offSupportOutsideInfinite_of_noSecondBoundedRegion (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hres : kc14_NoSecondBoundedRegion (mpl_orbitLoop K a)) :
    kc7_OffSupportOutsideInfinite K a :=
  kc13_offSupportOutsideInfinite_of_noFiniteHole K a R hRbox hbridge
    (kc14_noFiniteHole_of_noSecondBoundedRegion (mpl_orbitLoop K a) hres)


theorem kc14_unitCell_noSecondBoundedRegion :
    kc14_NoSecondBoundedRegion (mpl_orbitLoop unitCell ucBase) :=
  kc14_noSecondBoundedRegion_of_noFiniteHole (mpl_orbitLoop unitCell ucBase)
    kc13_unitCell_noFiniteHole


theorem kc14_unitCell_reachesFarLeftBeacon :
    kc12_ReachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1 :=
  kc14_reachesFarLeftBeacon_of_noSecondBoundedRegion (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc14_unitCell_noSecondBoundedRegion


theorem kc14_unitCell_no_finite_outside_component (z : Site 2)
    (hz : z ∉ (mpl_orbitLoop unitCell ucBase).support)
    (hzout : z ∉ jec_leftRegion (mpl_orbitLoop unitCell ucBase)) :
    ¬ (kc12_component (mpl_orbitLoop unitCell ucBase) z).Finite :=
  kc14_unitCell_noSecondBoundedRegion z hz hzout

end Walls
end StatMech
