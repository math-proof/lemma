/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Def.StatisticalMechanics.Code.Walls.wpjplanarjordan
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem wpj_winding_separation_of_bridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : wpj_PlaneDualityBridge Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
  obtain ⟨hoffIn, hoffOut, ⟨x, hxin⟩, ⟨y, hyout⟩, ⟨sIn, hcovIn⟩, ⟨sOut, hcovOut⟩⟩ := h
  exact fcb_offComplComponentCount_eq_two_of_covers Vc hoffIn hoffOut hxin hyout hcovIn hcovOut


theorem wpj_offComplJordanRegion_of_bridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : wpj_PlaneDualityBridge Vc) : fcb_OffComplJordanRegion Vc := by
  obtain ⟨hoffIn, hoffOut, ⟨x, hxin⟩, ⟨y, hyout⟩, ⟨sIn, hcovIn⟩, ⟨sOut, hcovOut⟩⟩ := h
  exact fcb_offComplJordanRegion_of_covers Vc hoffIn hoffOut hxin hyout hcovIn hcovOut


theorem wpj_jed_faithful_dual_count (P : PlanarZ2Subgraph) :
    whc_FaithfulDiscreteJordan P :=
  jed_faithfulDiscreteJordan P


theorem wpj_support_site_not_offSupport_vertex {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {s : Site 2} (hs : s ∈ Vc.support) : ¬ (s ∈ {z : Site 2 | z ∉ Vc.support}) := by
  simp only [Set.mem_setOf_eq, not_not]; exact hs


theorem wpj_basepoint_mem_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    a ∈ Vc.support := Vc.start_mem_support

end Lattice
end StatMech
