/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc10core.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Def.StatisticalMechanics.Code.Walls.kc12core.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc12_finiteComponent_top_blocked (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 + 1] : Site 2) ∈ Vc.support := by
  classical
  obtain ⟨w, hwC, hwmax⟩ :=
    Set.exists_max_image (kc12_component Vc z) (fun y => y 1) hfin ⟨z, Reachable.refl z⟩
  have hwreach : (offSupport Vc).Reachable z w := hwC
  refine ⟨w, hwreach, ?_⟩
  by_contra hup
  have hadj : (hypercubicLattice 2).Adj w ![w 0, w 1 + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w ![w 0, w 1 + 1] :=
    (offSupport_adj Vc w _).mpr ⟨hadj, hwoff, hup⟩
  have hupC : (![w 0, w 1 + 1] : Site 2) ∈ kc12_component Vc z := hwreach.trans hoffadj.reachable
  have hle := hwmax _ hupC
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hle
  omega


theorem kc12_finiteComponent_bottom_blocked (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 - 1] : Site 2) ∈ Vc.support := by
  classical
  obtain ⟨w, hwC, hwmin⟩ :=
    Set.exists_min_image (kc12_component Vc z) (fun y => y 1) hfin ⟨z, Reachable.refl z⟩
  have hwreach : (offSupport Vc).Reachable z w := hwC
  refine ⟨w, hwreach, ?_⟩
  by_contra hdown
  have hadj : (hypercubicLattice 2).Adj w ![w 0, w 1 - 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w ![w 0, w 1 - 1] :=
    (offSupport_adj Vc w _).mpr ⟨hadj, hwoff, hdown⟩
  have hdownC : (![w 0, w 1 - 1] : Site 2) ∈ kc12_component Vc z := hwreach.trans hoffadj.reachable
  have hle := hwmin _ hdownC
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hle
  omega


theorem kc12_finiteComponent_right_blocked (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 + 1, w 1] : Site 2) ∈ Vc.support := by
  classical
  obtain ⟨w, hwC, hwmax⟩ :=
    Set.exists_max_image (kc12_component Vc z) (fun y => y 0) hfin ⟨z, Reachable.refl z⟩
  have hwreach : (offSupport Vc).Reachable z w := hwC
  refine ⟨w, hwreach, ?_⟩
  by_contra hright
  have hadj : (hypercubicLattice 2).Adj w ![w 0 + 1, w 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w ![w 0 + 1, w 1] :=
    (offSupport_adj Vc w _).mpr ⟨hadj, hwoff, hright⟩
  have hrightC : (![w 0 + 1, w 1] : Site 2) ∈ kc12_component Vc z := hwreach.trans hoffadj.reachable
  have hle := hwmax _ hrightC
  simp only [Matrix.cons_val_zero] at hle
  omega


theorem kc12_finiteComponent_left_blocked (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 - 1, w 1] : Site 2) ∈ Vc.support := by
  classical
  obtain ⟨w, hwC, hwmin⟩ :=
    Set.exists_min_image (kc12_component Vc z) (fun y => y 0) hfin ⟨z, Reachable.refl z⟩
  have hwreach : (offSupport Vc).Reachable z w := hwC
  refine ⟨w, hwreach, ?_⟩
  by_contra hleft
  have hadj : (hypercubicLattice 2).Adj w ![w 0 - 1, w 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w ![w 0 - 1, w 1] :=
    (offSupport_adj Vc w _).mpr ⟨hadj, hwoff, hleft⟩
  have hleftC : (![w 0 - 1, w 1] : Site 2) ∈ kc12_component Vc z := hwreach.trans hoffadj.reachable
  have hle := hwmin _ hleftC
  simp only [Matrix.cons_val_zero] at hle
  omega


theorem kc12_finiteComponent_enclosed (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 + 1] : Site 2) ∈ Vc.support) ∧
    (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 - 1] : Site 2) ∈ Vc.support) ∧
    (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 + 1, w 1] : Site 2) ∈ Vc.support) ∧
    (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 - 1, w 1] : Site 2) ∈ Vc.support) :=
  ⟨kc12_finiteComponent_top_blocked Vc hz hfin,
   kc12_finiteComponent_bottom_blocked Vc hz hfin,
   kc12_finiteComponent_right_blocked Vc hz hfin,
   kc12_finiteComponent_left_blocked Vc hz hfin⟩


theorem kc12_offSupportOutsideInfinite_of_reachesFarLeft (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hres : kc12_ReachesFarLeftBeacon (mpl_orbitLoop K a) R) :
    kc7_OffSupportOutsideInfinite K a :=
  kc8_offSupportOutsideInfinite_of_offSupportReaches K a R hRbox hbridge
    (kc12_offSupportReaches_of_reachesFarLeft (mpl_orbitLoop K a) R hres)


theorem kc12_unitCell_reachesFarLeftBeacon :
    kc12_ReachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1 :=
  kc12_reachesFarLeftBeacon_of_offSupportReaches (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc8_unitCell_offSupportReaches


theorem kc12_unitCell_offSupportReaches_via_farLeft :
    kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 :=
  kc12_offSupportReaches_of_reachesFarLeft (mpl_orbitLoop unitCell ucBase) 1
    kc12_unitCell_reachesFarLeftBeacon


end Walls
end StatMech
