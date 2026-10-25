/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Def.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem fcb_offComplJordanRegion_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hyout : y ∉ jec_leftRegion Vc)
    {sIn sOut : Site 2}
    (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
    (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
    fcb_OffComplJordanRegion Vc :=
  ⟨⟨x, hxin, hoffIn x hxin⟩, ⟨y, hyout, hoffOut y hyout⟩,
    fcb_inside_conn_of_covers Vc hoffIn hcovIn,
    fcb_outside_conn_of_covers Vc hcovOut⟩


theorem fcb_two_components_of_region {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : fcb_OffComplJordanRegion Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
  obtain ⟨⟨x, hxin, hxoff⟩, ⟨y, hyout, hyoff⟩, hin, hout⟩ := h
  exact fcb_two_components_of_sides Vc hxin hxoff hyout hyoff hin hout


theorem fcb_offComplComponentCount_eq_faceCount_of_jordanRegion {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : fcb_OffComplJordanRegion Vc)
    {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
  rw [fcb_two_components_of_region Vc h, jcs_cycle_faceCount_eq_two c hc]


theorem fcb_self_component_side {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (v : {z : Site 2 // z ∉ Vc.support}) :
    ((v : Site 2) ∈ jec_leftRegion Vc ↔ (v : Site 2) ∈ jec_leftRegion Vc) :=
  Iff.rfl


theorem fcb_adj_sameSide {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (u ∈ jec_leftRegion Vc ↔ v ∈ jec_leftRegion Vc) := by
  have hadj' : (fcb_offComplGraph Vc).Adj ⟨u, hu⟩ ⟨v, hv⟩ := ⟨hadj, hu, hv⟩
  exact fcb_offCompl_sameSide Vc hadj'.reachable

end Lattice
end StatMech
