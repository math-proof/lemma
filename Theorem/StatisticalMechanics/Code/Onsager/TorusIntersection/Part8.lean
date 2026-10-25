/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_horizontalZBit_eq_zeroFlux_add
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) :
    ons_horizontalZBit F p =
      ons_zeroFluxHorizontal F p +
        if p.2 = 0 then ons_xFlux F (-1) else 0 := by
  unfold ons_zeroFluxHorizontal
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem ons_verticalZBit_eq_zeroFlux_add
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) :
    ons_verticalZBit F p =
      ons_zeroFluxVertical F p +
        if p.1 = 0 then ons_yFlux F (-1) else 0 := by
  unfold ons_zeroFluxVertical
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem ons_horizontalSeam_intersection_sum
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) :
    (∑ p : ZMod L × ZMod L,
      (if p.2 = 0 then ons_xFlux F (-1) else 0) *
        ons_verticalZBit G (p.1, p.2 - 1)) =
      ons_xFlux F (-1) * ons_yFlux G (-1) := by
  calc
    (∑ p : ZMod L × ZMod L,
      (if p.2 = 0 then ons_xFlux F (-1) else 0) *
        ons_verticalZBit G (p.1, p.2 - 1)) =
        ∑ x : ZMod L,
          ons_xFlux F (-1) * ons_verticalZBit G (x, -1) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = ons_xFlux F (-1) * ons_yFlux G (-1) := by
      unfold ons_yFlux
      rw [Finset.mul_sum]

theorem ons_verticalSeam_intersection_sum
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) :
    (∑ p : ZMod L × ZMod L,
      (if p.1 = 0 then ons_yFlux F (-1) else 0) *
        ons_horizontalZBit G (p.1 - 1, p.2)) =
      ons_yFlux F (-1) * ons_xFlux G (-1) := by
  calc
    (∑ p : ZMod L × ZMod L,
      (if p.1 = 0 then ons_yFlux F (-1) else 0) *
        ons_horizontalZBit G (p.1 - 1, p.2)) =
        ∑ y : ZMod L,
          ons_yFlux F (-1) * ons_horizontalZBit G (-1, y) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = ons_yFlux F (-1) * ons_xFlux G (-1) := by
      unfold ons_xFlux
      rw [Finset.mul_sum]

theorem ons_edgeCycleZIntersection_eq_flux
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
    ons_edgeCycleZIntersection F G =
      ons_xFlux F (-1) * ons_yFlux G (-1) +
        ons_yFlux F (-1) * ons_xFlux G (-1) := by
  unfold ons_edgeCycleZIntersection
  have hH : ∀ p : ZMod L × ZMod L, ons_horizontalZBit F p =
      ons_zeroFluxHorizontal F p +
        if p.2 = 0 then ons_xFlux F (-1) else 0 :=
    ons_horizontalZBit_eq_zeroFlux_add F
  have hV : ∀ p : ZMod L × ZMod L, ons_verticalZBit F p =
      ons_zeroFluxVertical F p +
        if p.1 = 0 then ons_yFlux F (-1) else 0 :=
    ons_verticalZBit_eq_zeroFlux_add F
  simp_rw [hH, hV]
  calc
    (∑ p : ZMod L × ZMod L,
      ((ons_zeroFluxHorizontal F p +
            if p.2 = 0 then ons_xFlux F (-1) else 0) *
          ons_verticalZBit G (p.1, p.2 - 1) +
        (ons_zeroFluxVertical F p +
            if p.1 = 0 then ons_yFlux F (-1) else 0) *
          ons_horizontalZBit G (p.1 - 1, p.2))) =
        (∑ p : ZMod L × ZMod L,
          (ons_zeroFluxHorizontal F p *
              ons_verticalZBit G (p.1, p.2 - 1) +
            ons_zeroFluxVertical F p *
              ons_horizontalZBit G (p.1 - 1, p.2))) +
        (∑ p : ZMod L × ZMod L,
          (if p.2 = 0 then ons_xFlux F (-1) else 0) *
            ons_verticalZBit G (p.1, p.2 - 1)) +
        (∑ p : ZMod L × ZMod L,
          (if p.1 = 0 then ons_yFlux F (-1) else 0) *
            ons_horizontalZBit G (p.1 - 1, p.2)) := by
          simp only [add_mul, Finset.sum_add_distrib]
          abel
    _ = ons_xFlux F (-1) * ons_yFlux G (-1) +
          ons_yFlux F (-1) * ons_xFlux G (-1) := by
      rw [ons_zeroFlux_intersection_eq_zero L F G hF hG,
        ons_horizontalSeam_intersection_sum L F G,
        ons_verticalSeam_intersection_sum L F G, zero_add]

theorem ons_edgeCycleIntersection_cast
    {L : ℕ} [NeZero L]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) :
    (ons_edgeCycleIntersection F G : ZMod 2) =
      ons_edgeCycleZIntersection F G := by
  unfold ons_edgeCycleIntersection ons_edgeCycleZIntersection
  rfl

theorem ons_homologyIntersection_cast_eq_flux
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) :
    (ons_homologyIntersection
        (ons_evenHomology L F) (ons_evenHomology L G) : ZMod 2) =
      ons_xFlux F (-1) * ons_yFlux G (-1) +
        ons_yFlux F (-1) * ons_xFlux G (-1) := by
  unfold ons_homologyIntersection
  rw [ons_evenHomology_fst_cast_eq_xFlux L F,
    ons_evenHomology_snd_cast_eq_yFlux L F,
    ons_evenHomology_fst_cast_eq_xFlux L G,
    ons_evenHomology_snd_cast_eq_yFlux L G]
  rfl

theorem ons_edgeCycleIntersection_eq_homologyIntersection
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
    ons_edgeCycleIntersection F G =
      ons_homologyIntersection
        (ons_evenHomology L F) (ons_evenHomology L G) := by
  have hz :
      (ons_edgeCycleIntersection F G : ZMod 2) =
        (ons_homologyIntersection
          (ons_evenHomology L F) (ons_evenHomology L G) : ZMod 2) := by
    have hcast := ons_edgeCycleIntersection_cast F G
    have hflux := ons_edgeCycleZIntersection_eq_flux L F G hF hG
    have hhom := ons_homologyIntersection_cast_eq_flux L F G
    exact hcast.trans (hflux.trans hhom.symm)
  exact_mod_cast hz

theorem ons_walk_edges_incCount_eq_zero_of_not_mem_support
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (z : V)
    (hz : z ∉ p.support) :
    incCount p.edges.toFinset z = 0 := by
  unfold incCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro edge hedge hzedge
  apply hz
  exact p.mem_support_of_mem_edges (List.mem_toFinset.mp hedge) hzedge

theorem ons_walk_edges_incCounts_disjoint_of_support_disjoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v x y : V} (p : G.Walk u v) (q : G.Walk x y)
    (hdisj : List.Disjoint p.support q.support) :
    ∀ z, incCount p.edges.toFinset z = 0 ∨
      incCount q.edges.toFinset z = 0 := by
  intro z
  by_cases hz : z ∈ p.support
  · right
    apply ons_walk_edges_incCount_eq_zero_of_not_mem_support q z
    intro hzq
    exact (List.disjoint_left.mp hdisj) hz hzq
  · left
    exact ons_walk_edges_incCount_eq_zero_of_not_mem_support p z hz

theorem ons_homologyIntersection_eq_zero_of_incCount_disjoint
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (hG : G ∈ evenSubgraphs (onsTorusGraph L))
    (hdisj : ∀ p, incCount F p = 0 ∨ incCount G p = 0) :
    ons_homologyIntersection
      (ons_evenHomology L F) (ons_evenHomology L G) = 0 := by
  rw [← ons_edgeCycleIntersection_eq_homologyIntersection L F G hF hG]
  exact ons_edgeCycleIntersection_eq_zero_of_incCount_disjoint F G hdisj

theorem ons_decEmbedWalk_originalHomology_isotropic
    (L : ℕ) [Fact (2 < L)]
    {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (p : (ons_decGraph L).Walk e e)
    (hq : q.IsCycle) (hp : p.IsCycle)
    (hqsnd : q.snd = ons_dartRev L d)
    (hpsnd : p.snd = ons_dartRev L e)
    (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
    ons_homologyIntersection
      (ons_evenHomology L (ons_walkOriginalEdges q))
      (ons_evenHomology L (ons_walkOriginalEdges p)) = 0 := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  have hqeven : (ons_decEmbedWalk L q).edges.toFinset ∈
      evenSubgraphs (onsTorusGraph (8 * L)) :=
    ons_cycle_edges_evenSubgraph (onsTorusGraph (8 * L))
      (ons_decEmbedWalk L q)
      (ons_decEmbedWalk_isCycle L q hq)
  have hpeven : (ons_decEmbedWalk L p).edges.toFinset ∈
      evenSubgraphs (onsTorusGraph (8 * L)) :=
    ons_cycle_edges_evenSubgraph (onsTorusGraph (8 * L))
      (ons_decEmbedWalk L p)
      (ons_decEmbedWalk_isCycle L p hp)
  have hsupp :=
    ons_decEmbedWalk_support_disjoint_of_toSubgraph L q p hdisj
  have hrefined :
      ons_homologyIntersection
        (ons_evenHomology (8 * L) (ons_decEmbedWalk L q).edges.toFinset)
        (ons_evenHomology (8 * L) (ons_decEmbedWalk L p).edges.toFinset) = 0 :=
    ons_homologyIntersection_eq_zero_of_incCount_disjoint
      (8 * L) _ _ hqeven hpeven
      (ons_walk_edges_incCounts_disjoint_of_support_disjoint
        (ons_decEmbedWalk L q) (ons_decEmbedWalk L p) hsupp)
  rw [ons_decEmbedWalk_evenHomology_eq L q hq hqsnd,
    ons_decEmbedWalk_evenHomology_eq L p hp hpsnd] at hrefined
  exact hrefined

theorem ons_decCycles_originalHomology_isotropic
    (L : ℕ) [Fact (2 < L)]
    {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (p : (ons_decGraph L).Walk e e)
    (hq : q.IsCycle) (hp : p.IsCycle)
    (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
    ons_homologyIntersection
      (ons_evenHomology L (ons_walkOriginalEdges q))
      (ons_evenHomology L (ons_walkOriginalEdges p)) = 0 := by
  obtain ⟨dq, q', hq', hqsnd, hqedges⟩ :=
    ons_decCycle_root_external q hq
  obtain ⟨dp, p', hp', hpsnd, hpedges⟩ :=
    ons_decCycle_root_external p hp
  have hqverts : q'.toSubgraph.verts = q.toSubgraph.verts := by
    ext z
    rw [q'.mem_verts_toSubgraph, q.mem_verts_toSubgraph,
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hq'.not_nil,
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hq.not_nil]
    constructor
    · rintro ⟨edge, hedge, hzedge⟩
      refine ⟨edge, ?_, hzedge⟩
      exact List.mem_toFinset.mp
        (hqedges.symm ▸ List.mem_toFinset.mpr hedge)
    · rintro ⟨edge, hedge, hzedge⟩
      refine ⟨edge, ?_, hzedge⟩
      exact List.mem_toFinset.mp
        (hqedges ▸ List.mem_toFinset.mpr hedge)
  have hpverts : p'.toSubgraph.verts = p.toSubgraph.verts := by
    ext z
    rw [p'.mem_verts_toSubgraph, p.mem_verts_toSubgraph,
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp'.not_nil,
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil]
    constructor
    · rintro ⟨edge, hedge, hzedge⟩
      refine ⟨edge, ?_, hzedge⟩
      exact List.mem_toFinset.mp
        (hpedges.symm ▸ List.mem_toFinset.mpr hedge)
    · rintro ⟨edge, hedge, hzedge⟩
      refine ⟨edge, ?_, hzedge⟩
      exact List.mem_toFinset.mp
        (hpedges ▸ List.mem_toFinset.mpr hedge)
  have hrootDisj : Disjoint q'.toSubgraph.verts p'.toSubgraph.verts := by
    rw [hqverts, hpverts]
    exact hdisj
  have hroot := ons_decEmbedWalk_originalHomology_isotropic
    L q' p' hq' hp' hqsnd hpsnd hrootDisj
  have hqorig : ons_walkOriginalEdges q' = ons_walkOriginalEdges q := by
    unfold ons_walkOriginalEdges ons_walkExternalEdges
    rw [hqedges]
  have hporig : ons_walkOriginalEdges p' = ons_walkOriginalEdges p := by
    unfold ons_walkOriginalEdges ons_walkExternalEdges
    rw [hpedges]
  rwa [hqorig, hporig] at hroot

theorem ons_decCycleFamily_originalHomology_isotropic
    (L : ℕ) [Fact (2 < L)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base : ι → ons_Dart L)
    (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i))
    (hcycle : ∀ i, (p i).IsCycle)
    (hverts : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i ↦ (p i).toSubgraph.verts)) :
    ∀ i j, i ≠ j →
      ons_homologyIntersection
        (ons_evenHomology L (ons_walkOriginalEdges (p i)))
        (ons_evenHomology L (ons_walkOriginalEdges (p j))) = 0 := by
  intro i j hij
  apply ons_decCycles_originalHomology_isotropic L
    (p i) (p j) (hcycle i) (hcycle j)
  exact hverts (Finset.mem_univ i) (Finset.mem_univ j) hij

end StatMech.Onsager
