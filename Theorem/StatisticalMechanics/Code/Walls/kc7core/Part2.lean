/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc6core.Part2
import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
import Theorem.StatisticalMechanics.Code.Walls.kc6localconstancy
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Def.StatisticalMechanics.Code.Walls.kc7core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc7_offSupportOutsideInK_of_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hres : kc7_OffSupportOutsideInfinite K a) :
    kc6_OffSupportOutsideInK K a := by
  intro z hzK hzsupp
  obtain ⟨hzmem, hinf⟩ := hres z hzK hzsupp
  have hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R := fun p hp => hRbox hp
  exact kc7_even_of_infiniteComponent (mpl_orbitLoop K a) R hsupp hzmem hinf


theorem kc7_interiorSubset_of_supportOdd_and_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hsupp : exc_SupportOddInK K a)
    (hres : kc7_OffSupportOutsideInfinite K a) :
    eaw_InteriorSubset K a :=
  kc6_interiorSubset_of_supportOdd_and_bridge K a hsupp
    (kc7_offSupportOutsideInK_of_infinite K a R hRbox hres)


theorem kc7_leftRegion_eq_of_supportOdd_winding_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hsupp : exc_SupportOddInK K a)
    (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a))
    (hres : kc7_OffSupportOutsideInfinite K a) :
    K = jec_leftRegion (mpl_orbitLoop K a) :=
  kc6_leftRegion_eq_of_core_and_winding K a
    (kc7_interiorSubset_of_supportOdd_and_infinite K a R hRbox hsupp hres) hwind


theorem kc7_bdEdgeMatch_of_supportOdd_winding_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hsupp : exc_SupportOddInK K a)
    (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a))
    (hres : kc7_OffSupportOutsideInfinite K a) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) :=
  kc6_bdEdgeMatch_of_core_and_winding K a
    (kc7_interiorSubset_of_supportOdd_and_infinite K a R hRbox hsupp hres) hwind


theorem kc7_offSupport_inside_subset_of_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hres : kc7_OffSupportOutsideInfinite K a) :
    ∀ z, z ∉ (mpl_orbitLoop K a).support →
      ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) → z ∈ K :=
  (kc6_bridge_iff_offSupport_inside_subset K a).mp
    (kc7_offSupportOutsideInK_of_infinite K a R hRbox hres)


theorem kc7_exterior_satisfies_residue_conclusion (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    {z : Site 2} (hz : z ∈ exterior 2 R) :
    ∃ hzmem : z ∈ (oc_supportSet (mpl_orbitLoop K a))ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet (mpl_orbitLoop K a))ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite := by
  have hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R := fun p hp => hRbox hp
  exact kc4_exterior_in_infiniteComponent (mpl_orbitLoop K a) R hsupp hz


theorem kc7_residue_conclusion_inhabited (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hKbox : K ⊆ box 2 R)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R) :
    ∃ z : Site 2, z ∉ K ∧ z ∉ (mpl_orbitLoop K a).support ∧
      ∃ hzmem : z ∈ (oc_supportSet (mpl_orbitLoop K a))ᶜ,
        (((hypercubicLattice 2).induce (oc_supportSet (mpl_orbitLoop K a))ᶜ).connectedComponentMk
          ⟨z, hzmem⟩).supp.Infinite := by
  
  have hbext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  refine ⟨beacon 2 R, ?_, ?_, ?_⟩
  · 
    intro hbK
    rw [exterior_eq_compl_box] at hbext
    exact hbext (hKbox hbK)
  · 
    have hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R := fun p hp => hRbox hp
    exact oc_exterior_offSupport (mpl_orbitLoop K a) R hsupp hbext
  · exact kc7_exterior_satisfies_residue_conclusion K a R hRbox hbext


theorem kc7_unitCell_offSupportOutsideInK : kc6_OffSupportOutsideInK unitCell ucBase :=
  kc6_unitCell_offSupportOutsideInK

end Walls
end StatMech
