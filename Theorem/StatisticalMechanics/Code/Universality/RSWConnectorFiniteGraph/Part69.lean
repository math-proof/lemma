/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part91
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorReachSet_subset_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_connectorReachSet gamma gamma' omega ⊆
      rlc_connectorFilledReachSet gamma gamma' omega := by
  intro z hz hExt
  obtain ⟨hzNot, _⟩ := hExt
  exact hzNot hz


theorem rlc_connectorExteriorSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorExteriorSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorExteriorSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_connectorExteriorSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨huNot, huComp⟩ := hu
  obtain ⟨hvNot, hvComp⟩ := hv
  have hcomp : ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)ᶜ).Reachable
      ⟨u, huNot⟩ ⟨v, hvNot⟩ :=
    ConnectedComponent.eq.mp (huComp.trans hvComp.symm)
  obtain ⟨w⟩ := hcomp
  let p : (hypercubicLattice 2).Walk u v :=
    w.map (SimpleGraph.Embedding.induce
      (rlc_connectorReachSet gamma gamma' omega)ᶜ).toHom
  have hpExt : ∀ z ∈ p.support,
      z ∈ rlc_connectorExteriorSet gamma gamma' omega := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce
        (rlc_connectorReachSet gamma gamma' omega)ᶜ).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    refine ⟨a.2, ?_⟩
    exact (ConnectedComponent.sound
      ⟨(w.takeUntil a ha).reverse⟩).trans huComp
  exact ⟨p.induce (rlc_connectorExteriorSet gamma gamma' omega) hpExt⟩


theorem rlc_connectorFilledReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_connectorFilledReachSet gamma gamma' omega).Finite := by
  let K := rlc_connectorReachSet gamma gamma' omega
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_connectorReachSet_finite gamma gamma' omega)
  apply (box_finite 2 R).subset
  intro z hzFill
  by_contra hzBox
  have hzExt : z ∈ exterior 2 R := by
    rw [exterior_eq_compl_box]
    exact hzBox
  have hzNotK : z ∈ Kᶜ := exterior_subset_compl K R hR hzExt
  have hzInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K R hR hzExt
  have hzComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩ = rlc_connectorExteriorComponent gamma gamma' omega :=
    (unique_infinite_component (by norm_num) K
      (rlc_connectorReachSet_finite gamma gamma' omega)).unique
        hzInf (rlc_connectorExteriorComponent_infinite gamma gamma' omega)
  exact hzFill ⟨hzNotK, hzComp⟩


theorem rlc_connectorExteriorSet_reachable_in_filledBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorExteriorSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorExteriorSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorExteriorSet gamma gamma' omega)) →g
      latticeMinusBarrier
        (rlc_connectorFilledReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_not_mem _ hab
        (by
          simp only [rlc_connectorFilledReachSet, Set.mem_compl_iff]
          exact not_not_intro a.2)
        (by
          simp only [rlc_connectorFilledReachSet, Set.mem_compl_iff]
          exact not_not_intro b.2)
  }
  have h := (rlc_connectorExteriorSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h

theorem rlc_walk_first_exit_set (A : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ (a b : Site 2) (p : (hypercubicLattice 2).Walk x a),
      (hypercubicLattice 2).Adj a b ∧
        (∀ z ∈ p.support, z ∈ A) ∧ b ∉ A := by
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ A
      · obtain ⟨u, v, q, huv, hq, hv⟩ := ih hb hy
        refine ⟨u, v, Walk.cons hab q, huv, ?_, hv⟩
        simp only [SimpleGraph.Walk.support_cons, List.forall_mem_cons]
        exact ⟨hx, hq⟩
      · exact ⟨a, b, Walk.nil, hab, by simpa, hb⟩


theorem rlc_connectorFilledReachSet_reaches_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u : Site 2}
    (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
    ∃ z : Site 2, ∃ hz : z ∈ rlc_connectorReachSet gamma gamma' omega,
      ((hypercubicLattice 2).induce
        (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable
          ⟨u, hu⟩
          ⟨z, rlc_connectorReachSet_subset_filled gamma gamma' omega hz⟩ := by
  let K := rlc_connectorReachSet gamma gamma' omega
  let H := rlc_connectorFilledReachSet gamma gamma' omega
  by_cases huK : u ∈ K
  · exact ⟨u, huK, Reachable.refl _⟩
  let A : Set (Site 2) := {z | ∃ hz : z ∈ Kᶜ,
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨u, huK⟩ ⟨z, hz⟩}
  have huA : u ∈ A := ⟨huK, Reachable.refl _⟩
  let k : Site 2 := gamma.1.1
  have hkPath : k ∈ rlc_pathVertices gamma.1 :=
    rlc_path_start_mem_vertices gamma.1
  have hkK : k ∈ K :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hkPath
  have hkNotA : k ∉ A := by
    rintro ⟨hkNot, _⟩
    exact hkNot hkK
  obtain ⟨w⟩ := pbs_reach_all u k
  obtain ⟨a, b, q, hab, hqA, hbNotA⟩ :=
    rlc_walk_first_exit_set A w huA hkNotA
  have haA : a ∈ A := hqA a q.end_mem_support
  obtain ⟨haNotK, hua⟩ := haA
  have hbK : b ∈ K := by
    by_contra hbNotK
    have habK : ((hypercubicLattice 2).induce Kᶜ).Adj
        ⟨a, haNotK⟩ ⟨b, hbNotK⟩ := hab
    exact hbNotA ⟨hbNotK, hua.trans habK.reachable⟩
  have hAinH : A ⊆ H := by
    intro z hzA hzExt
    obtain ⟨hzNotK, huz⟩ := hzA
    obtain ⟨_hzNotK', hzComp⟩ := hzExt
    have huComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨u, huK⟩ = rlc_connectorExteriorComponent gamma gamma' omega :=
      (ConnectedComponent.sound huz).trans hzComp
    exact hu ⟨huK, huComp⟩
  have hqH : ∀ z ∈ q.support, z ∈ H := by
    intro z hz
    exact hAinH (hqA z hz)
  have huaH : ((hypercubicLattice 2).induce H).Reachable
      ⟨u, hu⟩ ⟨a, hAinH ⟨haNotK, hua⟩⟩ := ⟨q.induce H hqH⟩
  have hbH : b ∈ H := rlc_connectorReachSet_subset_filled
    gamma gamma' omega hbK
  have habH : ((hypercubicLattice 2).induce H).Adj
      ⟨a, hAinH ⟨haNotK, hua⟩⟩ ⟨b, hbH⟩ := hab
  exact ⟨b, hbK, huaH.trans habH.reachable⟩


theorem rlc_connectorFilledReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨zu, hzu, huz⟩ :=
    rlc_connectorFilledReachSet_reaches_reachSet gamma gamma' omega hu
  obtain ⟨zv, hzv, hvz⟩ :=
    rlc_connectorFilledReachSet_reaches_reachSet gamma gamma' omega hv
  have hmiddle := (rlc_connectorReachSet_reachable
    gamma gamma' omega hzu hzv).map
      ((hypercubicLattice 2).induceHomOfLE
        (rlc_connectorReachSet_subset_filled gamma gamma' omega)).toHom
  exact huz.trans (hmiddle.trans hvz.symm)

theorem rlc_connectorFilledReachSet_reachable_in_barrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorFilledReachSet gamma gamma' omega)) →g
      latticeMinusBarrier
        (rlc_connectorFilledReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_connectorFilledReachSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h


theorem rlc_connectorFilledReachSet_faceBoundaryConnected {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    FaceBoundaryConnected (rlc_connectorFilledReachSet gamma gamma' omega)
      (phb_boundarySupport (rlc_connectorFilledReachSet gamma gamma' omega)
        (rlc_connectorFilledReachSet_finite gamma gamma' omega)) := by
  let H := rlc_connectorFilledReachSet gamma gamma' omega
  let hH := rlc_connectorFilledReachSet_finite gamma gamma' omega
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_connectorReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_connectorReachSet_subset_filled gamma gamma' omega hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  apply faceBoundaryConnected_of_connected_complement H hH hxH hyH
  · intro a b ha hb
    exact rlc_connectorFilledReachSet_reachable_in_barrier
      gamma gamma' omega ha hb
  · intro a b ha hb
    apply rlc_connectorExteriorSet_reachable_in_filledBarrier
      gamma gamma' omega
    · simpa [H, rlc_connectorFilledReachSet] using ha
    · simpa [H, rlc_connectorFilledReachSet] using hb


theorem rlc_connectorFilledBoundary_inside_mem_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {p q : Site 2}
    (hp : p ∈ rlc_connectorFilledReachSet gamma gamma' omega)
    (hq : q ∉ rlc_connectorFilledReachSet gamma gamma' omega)
    (hpq : (hypercubicLattice 2).Adj p q) :
    p ∈ rlc_connectorReachSet gamma gamma' omega := by
  let K := rlc_connectorReachSet gamma gamma' omega
  by_contra hpK
  have hqExt : q ∈ rlc_connectorExteriorSet gamma gamma' omega := by
    simpa [rlc_connectorFilledReachSet] using hq
  obtain ⟨hqK, hqComp⟩ := hqExt
  have hpqK : ((hypercubicLattice 2).induce Kᶜ).Adj
      ⟨p, hpK⟩ ⟨q, hqK⟩ := hpq
  have hpComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨p, hpK⟩ = rlc_connectorExteriorComponent gamma gamma' omega :=
    (ConnectedComponent.sound hpqK.reachable).trans hqComp
  exact hp ⟨hpK, hpComp⟩


theorem rlc_connectorFilled_edgeBoundary_subset_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {p q : Site 2}
    (hpq : (p, q) ∈ edgeBoundary 2
      (rlc_connectorFilledReachSet gamma gamma' omega)) :
    (p, q) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega) := by
  refine ⟨hpq.1, ?_⟩
  by_cases hp : p ∈ rlc_connectorFilledReachSet gamma gamma' omega
  · have hq : q ∉ rlc_connectorFilledReachSet gamma gamma' omega :=
      hpq.2.mp hp
    have hpK := rlc_connectorFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hp hq hpq.1
    have hqK : q ∉ rlc_connectorReachSet gamma gamma' omega := by
      intro hqK
      exact hq (rlc_connectorReachSet_subset_filled gamma gamma' omega hqK)
    exact iff_of_true hpK hqK
  · have hq : q ∈ rlc_connectorFilledReachSet gamma gamma' omega := by
      by_contra hq
      exact hp (hpq.2.mpr hq)
    have hqK := rlc_connectorFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hq hp hpq.1.symm
    have hpK : p ∉ rlc_connectorReachSet gamma gamma' omega := by
      intro hpK
      exact hp (rlc_connectorReachSet_subset_filled gamma gamma' omega hpK)
    simp [hpK, hqK]


theorem rlc_connectorFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma' omega) ≤
      faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega) := by
  intro f g hfg
  refine ⟨hfg.1, ?_⟩
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqFilled : (p, q) ∈ edgeBoundary 2
      (rlc_connectorFilledReachSet gamma gamma' omega) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hpqReach := rlc_connectorFilled_edgeBoundary_subset_reachSet
    gamma gamma' omega hpqFilled
  rw [hpq, bdEdge_mk]
  exact hpqReach.2


theorem rlc_connectorFilledFaceBoundary_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hf : f ∈ (faceBoundaryGraph
      (rlc_connectorFilledReachSet gamma gamma' omega)).support)
    (hg : g ∈ (faceBoundaryGraph
      (rlc_connectorFilledReachSet gamma gamma' omega)).support) :
    (faceBoundaryGraph
      (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable f g := by
  let H := rlc_connectorFilledReachSet gamma gamma' omega
  let hH := rlc_connectorFilledReachSet_finite gamma gamma' omega
  have hconn := rlc_connectorFilledReachSet_faceBoundaryConnected
    gamma gamma' omega
  rw [FaceBoundaryConnected, SimpleGraph.connected_iff] at hconn
  have hfT : f ∈ phb_boundarySupport H hH := by
    simpa [H, hH] using hf
  have hgT : g ∈ phb_boundarySupport H hH := by
    simpa [H, hH] using hg
  have hreach := hconn.1 ⟨f, hfT⟩ ⟨g, hgT⟩
  exact hreach.map (SimpleGraph.Embedding.induce
    (phb_boundarySupport H hH : Set (Site 2))).toHom


theorem rlc_connector_faceBoundary_preimage_not_trace_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Adj f g) :
    sharedPrimalEdge f g ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  intro htrace
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma'
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  rcases Finset.mem_union.mp htrace with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 (hpq ▸ hright)
    have hpReach := rlc_rightPathVertex_mem_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau) hends.1
    have hqReach := rlc_rightPathVertex_mem_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau) hends.2
    exact (hpqBoundary.2.mp hpReach) hqReach
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 (hpq ▸ hleft)
    have hambNo : rlc_connectorAmbientMixedConfig gamma gamma' tau ∉
        rlc_connectorEvent gamma gamma' := by
      intro hconn
      exact hno ((rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff
        gamma gamma' tau).mp hconn)
    have hpNot := rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector
      gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau)
      hambNo hends.1
    have hqNot := rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector
      gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau)
      hambNo hends.2
    exact hpNot (hpqBoundary.2.mpr hqNot)


theorem rlc_connector_reflectedFaceBoundary_preimage_not_trace_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  rw [rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg.1]
  exact rlc_connector_faceBoundary_preimage_not_trace_of_failure
    gamma gamma' tau hno hfg


theorem rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    {x y : Site 2}
    (a : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk x y) :
    let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
      (rlc_connectorAmbientMixedConfig gamma gamma' tau)
    let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau)
    ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges,
      rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  dsimp only
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let p := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  intro e he
  have hEdges : p.edges = (a.mapLe hle).edges.map
      (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (a.mapLe hle)
  rw [hEdges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  induction e0 using Sym2.inductionOn with
  | _ f g =>
      have hfgEdge : s(f, g) ∈ a.edges := by
        rw [a.edges_mapLe_eq_edges hle] at he0
        exact he0
      change rlc_pimsEdgeEquiv
        s(rlc_dualReflect f, rlc_dualReflect g) ∉ _
      exact rlc_connector_reflectedFaceBoundary_preimage_not_trace_of_failure
        gamma gamma' tau hno (a.adj_of_mem_edges hfgEdge)


theorem rlc_connectorEdge_endpoint_mem_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e) :
    z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
  rw [rlc_connectorEdges, Finset.mem_filter, mem_edgesWithinFinset] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he.1
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · simpa [rlc_connectorBox] using hx
  · simpa [rlc_connectorBox] using hy


theorem rlc_walk_support_mem_connectorBox_of_connectorEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {H : SimpleGraph (Site 2)} {x y : Site 2} (a : H.Walk x y)
    (hy : y ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
    (hedges : ∀ e ∈ a.edges,
      e ∈ rlc_connectorEdges gamma gamma') :
    ∀ z ∈ a.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact hy
  · exact rlc_connectorEdge_endpoint_mem_box gamma gamma'
      (hedges e he) hze


end
end StatMech.Universality
