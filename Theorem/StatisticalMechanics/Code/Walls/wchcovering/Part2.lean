/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Walls.wpjplanarjordan.Part2
import Theorem.StatisticalMechanics.Code.Walls.wocoutsidetop.Part4
import Def.StatisticalMechanics.Code.Walls.wchcovering
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wch_offComplJordanRegion_of_corrected (Vc : (hypercubicLattice 2).Walk a a)
    (h : wch_CorrectedBridge Vc) : fcb_OffComplJordanRegion Vc := by
  obtain ⟨⟨sIn, hsInmem, hsInoff, hcovIn⟩, ⟨sOut, hsOutmem, hsOutoff, hcovOut⟩⟩ := h
  refine ⟨⟨sIn, hsInmem, hsInoff⟩, ⟨sOut, hsOutmem, hsOutoff⟩, ?_, ?_⟩
  · 
    intro s t hs ht hsoff htoff
    have hsc : (offSupport Vc).Reachable sIn s :=
      (mem_offSupportComponent Vc).mp (hcovIn s hs hsoff)
    have htc : (offSupport Vc).Reachable sIn t :=
      (mem_offSupportComponent Vc).mp (hcovIn t ht htoff)
    exact offSupport_reachable_to_offSupportWalk Vc (hsc.symm.trans htc) hsoff
  · 
    intro s t hs ht hsoff htoff
    have hsc : (offSupport Vc).Reachable sOut s :=
      (mem_offSupportComponent Vc).mp (hcovOut s hs hsoff)
    have htc : (offSupport Vc).Reachable sOut t :=
      (mem_offSupportComponent Vc).mp (hcovOut t ht htoff)
    exact offSupport_reachable_to_offSupportWalk Vc (hsc.symm.trans htc) hsoff


theorem wch_winding_separation_of_corrected (Vc : (hypercubicLattice 2).Walk a a)
    (h : wch_CorrectedBridge Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 :=
  fcb_two_components_of_region Vc (wch_offComplJordanRegion_of_corrected Vc h)


theorem wch_exteriorCovering_of_noBoundedEven (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : woc_NoBoundedEvenComponent Vc) :
    (beacon 2 R) ∉ jec_leftRegion Vc ∧ (beacon 2 R) ∉ Vc.support ∧
      wch_ExteriorCovering Vc (beacon 2 R) := by
  have hbext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  refine ⟨oc_exterior_outside Vc R (fun p hp => hsupp hp) hbext,
    oc_exterior_offSupport Vc R hsupp hbext, ?_⟩
  intro z hzout hzoff
  
  have hinf : (offSupportComponent Vc z).Infinite := fun hfin => hzout (h z hzoff hfin)
  obtain ⟨e, he, hze⟩ := woc_infinite_reachesExterior Vc R hzoff hinf
  
  have hbe : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable (beacon 2 R) e :=
    oc_exterior_reachable_offSupport Vc R hsupp hbext he
  have hbz : (offSupport Vc).Reachable (beacon 2 R) z :=
    (woc_reachable_iff Vc).mpr (hbe.trans hze.symm)
  exact (mem_offSupportComponent Vc).mpr hbz


end Lattice
end StatMech
