/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint {n : Int}
    {f g x : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (hx : x ∈ sharedPrimalEdge f g)
    (hxRect : x ∈ rect (-2 * n) (2 * n) (-n) n) :
    rlc_dualReflect f ∈ rlc_twoChannelFullOuterBox n ∧
      rlc_dualReflect g ∈ rlc_twoChannelFullOuterBox n :=
  rlc_reflectedCarrierFaces_mem_crossedBoxInterior hfg hx hxRect


theorem rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
    rlc_dualReflect f ∈ rlc_twoChannelFullOuterBox n ∧
      rlc_dualReflect g ∈ rlc_twoChannelFullOuterBox n := by
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := by
    refine ⟨hpqAdj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  by_cases hp : p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega
  · have hpRect := rlc_twoChannelFullFilledReachSet_subset_connectorRect
      hn gamma gamma' omega hp
    apply rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint hfg.1
      (x := p) _ hpRect
    rw [hpq]
    exact Sym2.mem_mk_left p q
  · have hq : q ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
      by_contra hq
      exact hp (hpqBoundary.2.mpr hq)
    have hqRect := rlc_twoChannelFullFilledReachSet_subset_connectorRect
      hn gamma gamma' omega hq
    apply rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint hfg.1
      (x := q) _ hqRect
    rw [hpq]
    exact Sym2.mem_mk_right p q


theorem rlc_twoChannelFullFilledBoundaryWalk_reflect_mem_outerBox {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {x y z : Site 2}
    (a : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y)
    (hy : y ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hz : z ∈ a.support) :
    rlc_dualReflect z ∈ rlc_twoChannelFullOuterBox n := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · obtain ⟨g, hyg⟩ := hy
    exact (rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox
      hn gamma gamma' omega hyg).1
  · induction e using Sym2.inductionOn with
    | _ u v =>
        have huvAdj := a.adj_of_mem_edges he
        have hb := rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox
          hn gamma gamma' omega huvAdj
        rw [Sym2.mem_iff] at hze
        rcases hze with rfl | rfl
        · exact hb.1
        · exact hb.2


theorem rlc_twoChannelFullOuter_success_of_faithful_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    rlc_twoChannelFullOuterConfig gamma gamma' omega ∈
      rlc_twoChannelFullOuterConnectorEvent gamma gamma' := by
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hs := hfaith.right_axis_strict
    omega
  obtain ⟨x, y, hx, hy, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  obtain ⟨a⟩ := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hx hy
  let hle := rlc_twoChannelFullFilledBoundary_le_openFaceDual
    gamma gamma' omega
  let c := rlc_dualReflectOpenWalk
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega) (a.mapLe hle)
  have hcBox : ∀ z ∈ c.support,
      z ∈ rlc_twoChannelFullOuterBox n := by
    intro z hz
    change z ∈ ((a.mapLe hle).map
      (rlc_dualReflectOpenHom
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨f, hf, rfl⟩ := hz
    exact rlc_twoChannelFullFilledBoundaryWalk_reflect_mem_outerBox
      hn gamma gamma' omega a hy (by
        simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hf)
  let cOuter := c.induce (rlc_twoChannelFullOuterBox n) hcBox
  have hreach : (FK.openSub (rlc_twoChannelFullOuterGraph n)
      (rlc_twoChannelFullOuterConfig gamma gamma' omega)).Reachable
      ⟨rlc_dualReflect x, hcBox _ c.start_mem_support⟩
      ⟨rlc_dualReflect y, hcBox _ c.end_mem_support⟩ := by
    rw [rlc_openSub_twoChannelFullOuter_eq_induce]
    exact ⟨cOuter⟩
  exact ⟨⟨rlc_dualReflect x, hcBox _ c.start_mem_support⟩,
    ⟨rlc_dualReflect y, hcBox _ c.end_mem_support⟩,
    hxPath, hyPath, hreach⟩


theorem rlc_twoChannelReflectedDualEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_twoChannelReflectedDualEdge gamma gamma') := by
  intro e f hef
  have hemb := congrArg rlc_pimsEdgeEquiv hef
  simp only [rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge] at hemb
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  simpa [Ising.kwg_embeddedEdge,
    rlc_connectorTwoChannelAugmentedPlanarDomain] using hemb


end
end StatMech.Universality
