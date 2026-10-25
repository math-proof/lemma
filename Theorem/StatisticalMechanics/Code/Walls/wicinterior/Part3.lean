/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Walls.wnbenoboundedeven
import Theorem.StatisticalMechanics.Code.Walls.wchcovering.Part3
import Def.StatisticalMechanics.Code.Walls.wicinterior.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wic_interiorConnected_of_residue (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
    {sIn : Site 2} (hsInmem : sIn ∈ jec_leftRegion Vc) (hsInoff : sIn ∉ Vc.support)
    (hres : wic_LeftBoundaryConnected Vc) :
    wch_InteriorConnected Vc :=
  wic_interiorConnected_of_leftBoundaryConnected Vc R hsupp hsInmem hsInoff hres


theorem wic_winding_separation_of_residue (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
    {sIn : Site 2} (hsInmem : sIn ∈ jec_leftRegion Vc) (hsInoff : sIn ∉ Vc.support)
    (hres : wic_LeftBoundaryConnected Vc)
    (hNoBddEven : woc_NoBoundedEvenComponent Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
  have hsupp' : oc_supportSet Vc ⊆ box 2 R := fun p hp => hsupp p ((oc_mem_supportSet Vc p).mp hp)
  exact wch_winding_separation_of_residues Vc R hsupp'
    (wic_interiorConnected_of_residue Vc R hsupp hsInmem hsInoff hres) hNoBddEven

end Lattice
end StatMech
