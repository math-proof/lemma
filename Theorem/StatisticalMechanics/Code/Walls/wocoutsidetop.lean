/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem woc_offSupport_eq_ffc (Vc : (hypercubicLattice 2).Walk a a) :
    offSupport Vc = ffc_offSupportLattice (oc_supportSet Vc) := by
  ext x y
  simp [offSupport_adj, ffc_offSupportLattice_adj, oc_mem_supportSet]


theorem woc_reachable_iff (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2} :
    (offSupport Vc).Reachable x y ↔
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
  rw [woc_offSupport_eq_ffc]


theorem woc_beacon_row_ge_R (R : ℕ) : (R : ℤ) ≤ (beacon 2 R) 1 := by
  show (R : ℤ) ≤ (R : ℤ) + 1; omega


theorem woc_beacon_mem_exterior (R : ℕ) : beacon 2 R ∈ exterior 2 R :=
  beacon_mem_exterior R (by norm_num)


theorem woc_exterior_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {e : Site 2} (he : e ∈ exterior 2 R) :
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable e w :=
  ⟨beacon 2 R, woc_beacon_row_ge_R R,
    oc_exterior_reachable_offSupport Vc R hsupp he (woc_beacon_mem_exterior R)⟩


theorem woc_reachesExterior_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z e : Site 2} (hzoff : z ∉ Vc.support)
    (he : e ∈ exterior 2 R)
    (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
  obtain ⟨w, hwrow, hew⟩ := woc_exterior_reachesTop Vc R hsupp he
  have hzw : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z w := hze.trans hew
  obtain ⟨p, hp⟩ := (oc_offSupportLattice_reachable_iff Vc hzoff).mp hzw
  exact ⟨w, hwrow, p, hp⟩


theorem woc_reachesTop_of_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : oc_OutsideReachesExterior Vc R) :
    oc_OutsideReachesTop Vc R := by
  intro z hz
  obtain ⟨e, he, hze⟩ := h z hz
  
  have hzoff : z ∉ Vc.support := by
    rcases hze with ⟨w⟩
    cases w with
    | nil => exact oc_exterior_offSupport Vc R hsupp he
    | cons hadj _ => exact hadj.2.1
  exact woc_reachesExterior_reachesTop Vc R hsupp hzoff he hze


theorem woc_reachesTop_iff_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    oc_OutsideReachesTop Vc R ↔ oc_OutsideReachesExterior Vc R :=
  ⟨oc_outsideReachesExterior_of_reachesTop Vc R hsupp,
    woc_reachesTop_of_reachesExterior Vc R hsupp⟩


theorem woc_infiniteComponent_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z e : Site 2} (hzoff : z ∉ Vc.support)
    (he : e ∈ exterior 2 R)
    (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
    z ∉ jec_leftRegion Vc := by
  
  have hze' : (offSupport Vc).Reachable z e := (woc_reachable_iff Vc).mpr hze
  
  have heout : e ∉ jec_leftRegion Vc := oc_exterior_outside Vc R hsupp he
  
  exact fun hz => heout ((inside_sameRegion_offSupport Vc hze' hzoff).mp hz)


theorem woc_interiorComponent_bounded (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc)
    (hsoff : seed ∉ Vc.support) :
    (offSupportComponent Vc seed).Finite :=
  (egf_leftRegion_finite Vc R hsupp).subset
    (offSupportComponent_subset_interior Vc hseed hsoff)


theorem woc_interior_not_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hzin : z ∈ jec_leftRegion Vc)
    (hzoff : z ∉ Vc.support) :
    ¬ ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  rintro ⟨e, he, hze⟩
  exact woc_infiniteComponent_outside Vc R hsupp hzoff he hze hzin


end Lattice
end StatMech
