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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorTraceWiring_le_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorTraceWiring gamma gamma' ≤
      rlc_connectorSeparateWiring gamma gamma' := by
  intro x y hxy
  rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj]
  rcases Finset.mem_union.mp hxy.2 with hright | hleft
  · left
    rw [Lattice.boundaryCliqueGraph_adj]
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
    have hne : x ≠ y := fun h => hxy.1.ne (congrArg Subtype.val h)
    exact ⟨hne, hends.1, hends.2⟩
  · right
    rw [Lattice.boundaryCliqueGraph_adj]
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
    have hne : x ≠ y := fun h => hxy.1.ne (congrArg Subtype.val h)
    exact ⟨hne, hends.1, hends.2⟩


theorem rlc_connectorTraceWiring_reachable_right {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hx : rlc_connectorOnRight gamma x)
    (hy : rlc_connectorOnRight gamma y) :
    (rlc_connectorTraceWiring gamma gamma').Reachable x y := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hxW : (x : Site 2) ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (x : Site 2)).2 hx
  have hyW : (y : Site 2) ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (y : Site 2)).2 hy
  let wxy : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
    (W.takeUntil (x : Site 2) hxW).reverse.append
      (W.takeUntil (y : Site 2) hyW)
  have hwxyBox : ∀ z ∈ wxy.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
    intro z hz
    have hzW : z ∈ W.support := by
      dsimp only [wxy] at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse] at hz
      rcases hz with hz | hz
      · exact W.support_takeUntil_subset_support hxW (by simpa using hz)
      · exact W.support_takeUntil_subset_support hyW hz
    exact rlc_rightPathVertex_mem_connectorBox gamma
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).1 hzW)
  let wbox := wxy.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hwxyBox
  refine ⟨wbox.transfer (rlc_connectorTraceWiring gamma gamma') ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hexy : s((u : Site 2), (v : Site 2)) ∈ wxy.edges := by
        let hom := (SimpleGraph.Embedding.induce
          (G := hypercubicLattice 2)
          (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) wbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, by rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom wbox] at hmap
        simpa [hom, wbox] using hmap
      refine ⟨wxy.adj_of_mem_edges hexy, Finset.mem_union.mpr (Or.inl ?_)⟩
      exact rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1 (by
        dsimp only [wxy] at hexy
        simp only [SimpleGraph.Walk.edges_append,
          SimpleGraph.Walk.edges_reverse, List.mem_append,
          List.mem_reverse] at hexy
        rcases hexy with hexy | hexy
        · exact W.edges_takeUntil_subset hxW hexy
        · exact W.edges_takeUntil_subset hyW hexy)


theorem rlc_connectorTraceWiring_reachable_left {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hx : rlc_connectorOnLeft gamma' x)
    (hy : rlc_connectorOnLeft gamma' y) :
    (rlc_connectorTraceWiring gamma gamma').Reachable x y := by
  let W := rlc_ambientCrossingWalk gamma'.1
  have hxW : (x : Site 2) ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (x : Site 2)).2 hx
  have hyW : (y : Site 2) ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (y : Site 2)).2 hy
  let wxy : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
    (W.takeUntil (x : Site 2) hxW).reverse.append
      (W.takeUntil (y : Site 2) hyW)
  have hwxyBox : ∀ z ∈ wxy.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
    intro z hz
    have hzW : z ∈ W.support := by
      dsimp only [wxy] at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse] at hz
      rcases hz with hz | hz
      · exact W.support_takeUntil_subset_support hxW (by simpa using hz)
      · exact W.support_takeUntil_subset_support hyW hz
    exact rlc_leftPathVertex_mem_connectorBox gamma'
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).1 hzW)
  let wbox := wxy.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hwxyBox
  refine ⟨wbox.transfer (rlc_connectorTraceWiring gamma gamma') ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hexy : s((u : Site 2), (v : Site 2)) ∈ wxy.edges := by
        let hom := (SimpleGraph.Embedding.induce
          (G := hypercubicLattice 2)
          (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) wbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, by rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom wbox] at hmap
        simpa [hom, wbox] using hmap
      refine ⟨wxy.adj_of_mem_edges hexy, Finset.mem_union.mpr (Or.inr ?_)⟩
      exact rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1 (by
        dsimp only [wxy] at hexy
        simp only [SimpleGraph.Walk.edges_append,
          SimpleGraph.Walk.edges_reverse, List.mem_append,
          List.mem_reverse] at hexy
        rcases hexy with hexy | hexy
        · exact W.edges_takeUntil_subset hxW hexy
        · exact W.edges_takeUntil_subset hyW hexy)

theorem rlc_reachable_of_step_reachable
    {V : Type*} {G K : SimpleGraph V}
    (hstep : ∀ {x y}, G.Adj x y → K.Reachable x y)
    {x y : V} (hxy : G.Reachable x y) : K.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons huv p ih => exact (hstep huv).trans ih


theorem rlc_connectorTraceWiring_reachable_iff_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (x y : RlcConnectorVertex n) :
    (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y ↔
      (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable x y := by
  constructor
  · exact Reachable.mono
      (sup_le_sup_left
        (rlc_connectorTraceWiring_le_separateWiring gamma gamma') H)
  · intro hxy
    apply rlc_reachable_of_step_reachable
      (G := H ⊔ rlc_connectorSeparateWiring gamma gamma')
      (K := H ⊔ rlc_connectorTraceWiring gamma gamma') ?_ hxy
    intro u v huv
    rcases huv with hH | hsep
    · exact (show (H ⊔ rlc_connectorTraceWiring gamma gamma').Adj u v
        from Or.inl hH).reachable
    · rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
      rcases hsep with hright | hleft
      · rw [Lattice.boundaryCliqueGraph_adj] at hright
        exact (rlc_connectorTraceWiring_reachable_right gamma gamma'
          hright.2.1 hright.2.2).mono le_sup_right
      · rw [Lattice.boundaryCliqueGraph_adj] at hleft
        exact (rlc_connectorTraceWiring_reachable_left gamma gamma'
          hleft.2.1 hleft.2.2).mono le_sup_right


end
end StatMech.Universality
