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
import Def.StatisticalMechanics.Code.Walls.wocoutsidetop.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem woc_infinite_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2} (_hzoff : z ∉ Vc.support)
    (hinf : (offSupportComponent Vc z).Infinite) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  
  have hnotsub : ¬ offSupportComponent Vc z ⊆ box 2 R := by
    intro hsub
    exact hinf ((box_finite 2 R).subset hsub)
  rw [Set.not_subset] at hnotsub
  obtain ⟨e, hemem, hebox⟩ := hnotsub
  have heext : e ∈ exterior 2 R := by rw [exterior_eq_compl_box]; exact hebox
  
  have hze : (offSupport Vc).Reachable z e := (mem_offSupportComponent Vc).mp hemem
  exact ⟨e, heext, (woc_reachable_iff Vc).mp hze⟩


theorem woc_residue_of_noBoundedEven (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
    (h : woc_NoBoundedEvenComponent Vc) :
    woc_OutsideReachesExterior_residue Vc R := by
  intro z hz
  have hzoff : z ∉ Vc.support := hoffOut z hz
  
  have hinf : (offSupportComponent Vc z).Infinite := by
    intro hfin
    exact hz (h z hzoff hfin)
  exact woc_infinite_reachesExterior Vc R hzoff hinf


theorem woc_reachesTop_of_noBoundedEven (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
    (h : woc_NoBoundedEvenComponent Vc) :
    oc_OutsideReachesTop Vc R :=
  woc_reachesTop_of_residue Vc R hsupp (woc_residue_of_noBoundedEven Vc R hoffOut h)


theorem woc_two_components_of_noBoundedEven (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
    (h : woc_NoBoundedEvenComponent Vc) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  oc_two_components_of_reachesTop Vc R hsupp hp hq hInOff
    (woc_reachesTop_of_noBoundedEven Vc R hsupp hoffOut h)


theorem woc_interior_satisfies_residue (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hzin : z ∈ jec_leftRegion Vc)
    (hzoff : z ∉ Vc.support) :
    (offSupportComponent Vc z).Finite ∧ z ∈ jec_leftRegion Vc :=
  ⟨woc_interiorComponent_bounded Vc R hsupp hzin hzoff, hzin⟩

end Lattice
end StatMech
