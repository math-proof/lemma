/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OutsideReachesClose.Part2
import Def.StatisticalMechanics.Code.Lattice.ExteriorCoveredClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem ecc_rightStep_of_rightDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hdodge : ecc_RightDodge Vc R) : ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  by_cases hnb : (![z 0 + 1, z 1] : Site 2) ∈ Vc.support
  · exact hdodge z hzout hzoff hzR hnb
  · exact ⟨![z 0 + 1, z 1], by simp, ecc_rightNeighbor_step Vc hzoff hnb⟩


theorem ecc_rightStep_of_rightNeighbor_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hnb : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
        (![z 0 + 1, z 1] : Site 2) ∉ Vc.support) :
    ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  exact ⟨![z 0 + 1, z 1], by simp,
    ecc_rightNeighbor_step Vc hzoff (hnb z hzout hzoff hzR)⟩


theorem ecc_rightStep_of_floodFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hflood : oc_OutsideReachesExterior Vc R) :
    ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  obtain ⟨e, heExt, hreach⟩ := hflood z hzout
  
  set u : Site 2 := ![(R : ℤ) + 1 + max (z 0) 0, z 1] with hu
  have huExt : u ∈ exterior 2 R := by
    refine oc_mem_exterior_of_col_high R ?_
    rw [hu]; simp only [Matrix.cons_val_zero]
    have : (0 : ℤ) ≤ max (z 0) 0 := le_max_right _ _
    omega
  have hprog : z 0 < u 0 := by
    rw [hu]; simp only [Matrix.cons_val_zero]
    have h1 : z 0 ≤ max (z 0) 0 := le_max_left _ _
    have hR : (0 : ℤ) ≤ (R : ℤ) := by positivity
    omega
  have hmid : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable e u :=
    oc_exterior_reachable_offSupport Vc R hsupp heExt huExt
  have hzu_ffc : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z u := hreach.trans hmid
  exact ⟨u, hprog, orc_offSupport_reachable_of_offSupportLattice Vc hzoff hzu_ffc⟩


theorem ecc_rightStep_iff_exteriorCovered (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R) (hbOff : beacon ∉ Vc.support) :
    ecc_RightStep Vc R ↔ orc_ExteriorCovered Vc beacon := by
  constructor
  · intro hstep
    exact ecc_exteriorCovered_of_rightStep Vc R hsupp hoffOut hbExt hstep
  · intro hcov
    exact ecc_rightStep_of_floodFill Vc R hsupp
      (orc_outsideReachesExterior_of_exteriorCovered Vc R hbExt hbOff hcov)

end Lattice
end StatMech
