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
import Def.StatisticalMechanics.Code.Walls.kc12core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc12_offSupportReaches_of_reachesFarLeft (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hres : kc12_ReachesFarLeftBeacon Vc R) :
    kc5_OffSupportReachesExterior Vc R := by
  intro z hzoff hzout
  obtain ⟨p, hp⟩ := hres z hzoff hzout
  refine ⟨![-((R : ℤ) + 1), 0], kc12_farLeftBeacon_mem_exterior R, ?_⟩
  have hzc : z ∈ (oc_supportSet Vc)ᶜ := by simpa [oc_supportSet] using hzoff
  rw [ffc_reachable_iff_offSupportWalk hzc]
  exact ⟨p, fun u hu => by simpa [oc_supportSet] using hp u hu⟩


theorem kc12_exterior_reaches_farLeftBeacon (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {e : Site 2} (heExt : e ∈ exterior 2 R) :
    ∃ p : (hypercubicLattice 2).Walk e ![-((R : ℤ) + 1), 0], ∀ u ∈ p.support, u ∉ Vc.support := by
  set F : Set (Site 2) := {z | z ∈ Vc.support} with hF
  have hFbox : F ⊆ box 2 R := fun q hq => hsupp ((oc_mem_supportSet Vc q).mpr hq)
  have hsub : exterior 2 R ⊆ Fᶜ := exterior_subset_compl F R hFbox
  have hbext : (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := kc12_farLeftBeacon_mem_exterior R
  have hreach := box_exterior_connected R (by norm_num) e ![-((R : ℤ) + 1), 0] heExt hbext
  have hreachF :
      ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨e, hsub heExt⟩
        ⟨![-((R : ℤ) + 1), 0], hsub hbext⟩ := by
    have := hreach.map ((hypercubicLattice 2).induceHomOfLE hsub).toHom
    simpa using this
  exact exc_reachable_compl_to_offSupport_walk F (hsub heExt) (hsub hbext) hreachF


theorem kc12_reachesFarLeftBeacon_of_offSupportReaches (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (htgt : kc5_OffSupportReachesExterior Vc R) :
    kc12_ReachesFarLeftBeacon Vc R := by
  intro z hzoff hzout
  obtain ⟨e, heExt, hreach⟩ := htgt z hzoff hzout
  
  have hzc : z ∈ (oc_supportSet Vc)ᶜ := by simpa [oc_supportSet] using hzoff
  obtain ⟨p1, hp1⟩ := (ffc_reachable_iff_offSupportWalk hzc).mp hreach
  have hp1' : ∀ u ∈ p1.support, u ∉ Vc.support := fun u hu => by
    simpa [oc_supportSet] using hp1 u hu
  
  obtain ⟨p2, hp2⟩ := kc12_exterior_reaches_farLeftBeacon Vc R hsupp heExt
  refine ⟨p1.append p2, ?_⟩
  intro u hu
  rw [Walk.mem_support_append_iff] at hu
  rcases hu with h | h
  · exact hp1' u h
  · exact hp2 u h


theorem kc12_reachesFarLeftBeacon_iff_offSupportReaches (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    kc12_ReachesFarLeftBeacon Vc R ↔ kc5_OffSupportReachesExterior Vc R :=
  ⟨kc12_offSupportReaches_of_reachesFarLeft Vc R,
   kc12_reachesFarLeftBeacon_of_offSupportReaches Vc R hsupp⟩


theorem kc12_outsideOffSupportInfinite_of_reachesFarLeft (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hres : kc12_ReachesFarLeftBeacon Vc R) :
    kc5_OutsideOffSupportInfinite Vc :=
  kc8_outsideOffSupportInfinite_of_offSupportReaches Vc R hsupp
    (kc12_offSupportReaches_of_reachesFarLeft Vc R hres)


theorem kc12_reachesFarLeftBeacon_iff_outsideOffSupportInfinite
    (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    kc12_ReachesFarLeftBeacon Vc R ↔ kc5_OutsideOffSupportInfinite Vc := by
  constructor
  · exact kc12_outsideOffSupportInfinite_of_reachesFarLeft Vc R hsupp
  · intro hinf
    exact kc12_reachesFarLeftBeacon_of_offSupportReaches Vc R hsupp
      (kc5_offSupportReaches_of_corrected Vc R hsupp hinf)


theorem kc12_offSupport_reachable_offSupport (Vc : (hypercubicLattice 2).Walk a a)
    {z w : Site 2} (hz : z ∉ Vc.support) (h : (offSupport Vc).Reachable z w) :
    w ∉ Vc.support := by
  obtain ⟨p, hp⟩ := offSupport_reachable_to_offSupportWalk Vc h hz
  exact hp w p.end_mem_support


end Walls
end StatMech
