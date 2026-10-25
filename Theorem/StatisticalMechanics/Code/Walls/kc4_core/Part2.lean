/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc3_offsupportreaches
import Theorem.StatisticalMechanics.Code.Walls.kc4_eulerone.Part2
import Theorem.StatisticalMechanics.Code.Walls.kc4_orbitiscycle
import Def.StatisticalMechanics.Code.Walls.kc4_core.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc4_outsideReachesExterior_of_infinite (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hres : kc4_OutsideInInfiniteComponent Vc) :
    oc_OutsideReachesExterior Vc R := by
  intro z hzOut
  obtain ⟨hzmem, hinf⟩ := hres z hzOut
  exact kc4_reaches_exterior_of_infiniteComponent Vc R hsupp hzmem hinf


theorem kc4_infinite_of_outsideReachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hflood : oc_OutsideReachesExterior Vc R) :
    kc4_OutsideInInfiniteComponent Vc := by
  intro z hzOut
  obtain ⟨e, heExt, hreach⟩ := hflood z hzOut
  
  have hzoff : z ∉ Vc.support := by
    rcases hreach with ⟨w⟩
    cases w with
    | nil => exact oc_exterior_offSupport Vc R hsupp heExt
    | cons hadj _ => exact hadj.2.1
  have hzmem : z ∈ (oc_supportSet Vc)ᶜ := by simpa [oc_supportSet] using hzoff
  refine ⟨hzmem, ?_⟩
  
  obtain ⟨p, hp⟩ := (ffc_reachable_iff_offSupportWalk (B := oc_supportSet Vc) hzmem).mp hreach
  have hemem : e ∈ (oc_supportSet Vc)ᶜ := by
    have := hp e p.end_mem_support; simpa [oc_supportSet] using this
  have hindReach :
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).Reachable ⟨z, hzmem⟩ ⟨e, hemem⟩ :=
    walk_induce_reachable (hypercubicLattice 2) ((oc_supportSet Vc)ᶜ) p (fun w hw => hp w hw)
      hzmem hemem
  
  have hcompEq :
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩ =
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨e, hemem⟩ :=
    ConnectedComponent.sound hindReach
  rw [hcompEq]
  exact kc4_extComponent_infinite Vc R hsupp heExt hemem


theorem kc4_outsideReachesExterior_iff_infinite (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    oc_OutsideReachesExterior Vc R ↔ kc4_OutsideInInfiniteComponent Vc :=
  ⟨kc4_infinite_of_outsideReachesExterior Vc R hsupp,
   kc4_outsideReachesExterior_of_infinite Vc R hsupp⟩


theorem kc4_orbit_outsideReachesExterior_of_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hres : kc4_OutsideInInfiniteComponent (mpl_orbitLoop K a)) :
    oc_OutsideReachesExterior (mpl_orbitLoop K a) R :=
  kc4_outsideReachesExterior_of_infinite (mpl_orbitLoop K a) R hRbox hres


theorem kc4_exc_offSupportReaches_of_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hint : eaw_InteriorSubset K a)
    (hres : kc4_OutsideInInfiniteComponent (mpl_orbitLoop K a)) :
    exc_OffSupportReachesExterior K a :=
  kc3_offSupportReachesExterior_of_interiorSubset_and_outside K a R hRbox hint
    (kc4_orbit_outsideReachesExterior_of_infinite K a R hRbox hres)


theorem kc4_exterior_in_infiniteComponent (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite := by
  have hzmem : z ∈ (oc_supportSet Vc)ᶜ := by
    have := oc_exterior_offSupport Vc R hsupp hz; simpa [oc_supportSet] using this
  exact ⟨hzmem, kc4_extComponent_infinite Vc R hsupp hz hzmem⟩


theorem kc4_residue_nonvacuous (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∉ jec_leftRegion Vc ∧
      ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
        (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
          ⟨z, hzmem⟩).supp.Infinite :=
  ⟨oc_exterior_outside Vc R hsupp hz, kc4_exterior_in_infiniteComponent Vc R hsupp hz⟩


theorem kc4_orbitLoop_isCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitLoop K a).IsCycle :=
  kc4_OrbitIsCycle K a hp hinj


theorem kc4_contour_eulerOne {p : ℕ} (hp : 3 ≤ p) : kc4_contourEulerChar p = 1 :=
  kc4_eulerOne hp

end Walls
end StatMech
