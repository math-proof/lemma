/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.ClusterDualContour
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem ccs_closedLoop_leftRegion_bdEdge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd


theorem ccs_closedLoop_inside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (h : ¬ Even (jec_rayCount z Vc)) : z ∈ jec_leftRegion Vc :=
  h


theorem ccs_closedLoop_outside_far {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  exact jec_ray_even_far Vc z hfar


theorem ccs_closedLoop_outside_left {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hleft : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not, jec_rayCount_eq_zero_of_right z Vc hleft]
  exact Even.zero


theorem ccs_closedLoop_separation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (inside outside : Set (Site 2))
    (hin : ∀ z ∈ inside, ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z ∈ outside, Even (jec_rayCount z Vc)) :
    jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} inside outside := by
  refine ⟨jec_leftRegion Vc, ?_, ?_, ?_⟩
  · 
    intro z hz; exact hin z hz
  · 
    intro z hz; rw [jec_mem_leftRegion, not_not]; exact hout z hz
  · 
    intro u v _huD _hvD hadj huS hvS
    refine ccs_closedLoop_leftRegion_bdEdge Vc hadj ?_
    rw [bdEdge_mk]; exact ⟨fun _ => hvS, fun _ => huS⟩


theorem ccs_closedLoop_separatingSide_forces_cross {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (inside outside : Set (Site 2))
    (hin : ∀ z ∈ inside, ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z ∈ outside, Even (jec_rayCount z Vc))
    {x y : Site 2} (hx : x ∈ inside) (hy : y ∈ outside)
    (w : (hypercubicLattice 2).Walk x y) :
    ∃ z ∈ w.support, z ∈ Vc.support :=
  jcu_separatingSide_forces_cross (ccs_closedLoop_separation Vc inside outside hin hout) hx hy w
    (fun z _ => Set.mem_univ z)


theorem ccs_closedLoop_hasSeparatingSide {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1) :
    jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} {p} {q} := by
  refine ccs_closedLoop_separation Vc {p} {q} ?_ ?_
  · intro z hz; rw [Set.mem_singleton_iff] at hz; subst z; exact hp
  · intro z hz; rw [Set.mem_singleton_iff] at hz; subst z; exact jec_ray_even_far Vc q hq


theorem ccs_closedLoop_two_components {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  have hpS : p ∈ jec_leftRegion Vc := hp
  have hqS : q ∉ jec_leftRegion Vc := ccs_closedLoop_outside_far Vc hq
  exact jcs_two_components_of_sides (jec_leftRegion Vc) hpS hqS hin hout


end Lattice
end StatMech
