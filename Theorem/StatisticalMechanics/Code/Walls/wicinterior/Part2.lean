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
import Def.StatisticalMechanics.Code.Walls.wicinterior
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wic_reaches_leftBoundary (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
    {z : Site 2} (hz : z ∈ jec_leftRegion Vc) (hzoff : z ∉ Vc.support) :
    ∃ w ∈ wic_leftBoundary Vc, (offSupport Vc).Reachable z w := by
  obtain ⟨c₀, _, hreach, hint, hoff, hleft⟩ := wic_marchLeft Vc R hsupp hz hzoff
  refine ⟨(![c₀, z 1] : Site 2), ⟨hint, hoff, ?_⟩, hreach⟩
  simpa using hleft


theorem wic_interiorConnected_of_leftBoundaryConnected (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
    {sIn : Site 2} (hsInmem : sIn ∈ jec_leftRegion Vc) (hsInoff : sIn ∉ Vc.support)
    (hLB : ∀ u v : Site 2, u ∈ wic_leftBoundary Vc → v ∈ wic_leftBoundary Vc →
        (offSupport Vc).Reachable u v) :
    wch_InteriorConnected Vc := by
  rw [wch_interiorConnected_iff Vc hsInmem hsInoff]
  intro s t hs ht hsoff htoff
  obtain ⟨u, hu, hsu⟩ := wic_reaches_leftBoundary Vc R hsupp hs hsoff
  obtain ⟨v, hv, htv⟩ := wic_reaches_leftBoundary Vc R hsupp ht htoff
  exact (hsu.trans (hLB u v hu hv)).trans htv.symm


theorem wic_interiorConnected_of_hubReaches (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
    {hub : Site 2} (hhubmem : hub ∈ jec_leftRegion Vc) (hhuboff : hub ∉ Vc.support)
    (hhub : ∀ w ∈ wic_leftBoundary Vc, (offSupport Vc).Reachable hub w) :
    wch_InteriorConnected Vc := by
  refine wic_interiorConnected_of_leftBoundaryConnected Vc R hsupp hhubmem hhuboff ?_
  intro u v hu hv
  exact (hhub u hu).symm.trans (hhub v hv)


end Lattice
end StatMech
