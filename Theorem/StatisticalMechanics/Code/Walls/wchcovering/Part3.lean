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
import Def.StatisticalMechanics.Code.Walls.wchcovering.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wch_winding_separation_of_residues (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hIntConn : wch_InteriorConnected Vc)
    (hNoBddEven : woc_NoBoundedEvenComponent Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
  refine wch_winding_separation_of_corrected Vc ⟨hIntConn, ?_⟩
  obtain ⟨h1, h2, h3⟩ := wch_exteriorCovering_of_noBoundedEven Vc R hsupp hNoBddEven
  exact ⟨beacon 2 R, h1, h2, h3⟩


theorem wch_interiorConnected_iff (Vc : (hypercubicLattice 2).Walk a a)
    {sIn : Site 2} (hsInmem : sIn ∈ jec_leftRegion Vc) (hsInoff : sIn ∉ Vc.support) :
    wch_InteriorConnected Vc ↔
      ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support → (offSupport Vc).Reachable s t := by
  constructor
  · rintro ⟨seed, _, hseedoff, hcov⟩ s t hs ht hsoff htoff
    have hsc : (offSupport Vc).Reachable seed s := (mem_offSupportComponent Vc).mp (hcov s hs hsoff)
    have htc : (offSupport Vc).Reachable seed t := (mem_offSupportComponent Vc).mp (hcov t ht htoff)
    exact hsc.symm.trans htc
  · intro hconn
    refine ⟨sIn, hsInmem, hsInoff, ?_⟩
    intro z hz hzoff
    exact (mem_offSupportComponent Vc).mpr (hconn sIn z hsInmem hz hsInoff hzoff)

end Lattice
end StatMech
