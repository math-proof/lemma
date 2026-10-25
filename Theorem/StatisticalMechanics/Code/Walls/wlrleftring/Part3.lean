/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.wicinterior.Part3
import Def.StatisticalMechanics.Code.Walls.wlrleftring.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wlr_leftBoundaryConnected_of_innerRingConnected (Vc : (hypercubicLattice 2).Walk a a)
    (h : wlr_InnerRingConnected Vc) : wic_LeftBoundaryConnected Vc := by
  intro u v hu hv
  exact h u v (wlr_leftBoundary_subset_innerRing Vc hu) (wlr_leftBoundary_subset_innerRing Vc hv)


theorem wlr_winding_separation_of_innerRing (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
    {sIn : Site 2} (hsInmem : sIn ∈ jec_leftRegion Vc) (hsInoff : sIn ∉ Vc.support)
    (hres : wlr_InnerRingConnected Vc)
    (hNoBddEven : woc_NoBoundedEvenComponent Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 :=
  wic_winding_separation_of_residue Vc R hsupp hsInmem hsInoff
    (wlr_leftBoundaryConnected_of_innerRingConnected Vc hres) hNoBddEven


theorem wlr_support_connected (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hu : u ∈ Vc.support) (hv : v ∈ Vc.support) :
    ∃ p : (hypercubicLattice 2).Walk u v, ∀ z ∈ p.support, z ∈ Vc.support := by
  refine ⟨(Vc.takeUntil u hu).reverse.append (Vc.takeUntil v hv), ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_append] at hz
  rcases List.mem_append.mp hz with h | h
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h
    exact Vc.support_takeUntil_subset_support hu h
  · exact Vc.support_takeUntil_subset_support hv (List.tail_subset _ h)


end Lattice
end StatMech
