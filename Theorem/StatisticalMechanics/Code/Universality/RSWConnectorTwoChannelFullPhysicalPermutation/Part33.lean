/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part33
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue
    {n : Int} (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj f g)
    (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f))
    (hfailure :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure
        gamma gamma' B f g) :
    RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
      gamma gamma' A B f g := by
  rcases
      rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_target_or_sourceTraceResidue
        gamma gamma' A B hAright hAleft hfg hfailure with
    htarget | ⟨target, htarget, hcross, hsource⟩
  · exact Or.inl htarget
  · refine Or.inr ⟨target, htarget, hcross, ?_⟩
    simpa [RlcTwoChannelFullPhysicalReflectedLeftTerminalReducedSourceResidue]
      using
        (rlc_twoChannelFullPhysical_reflectedLeftTerminalSourceResidue_rightTrace_or_boxWall
          hn gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
            (rlc_twoChannelFullPhysicalCutInteriorConfig_failure
              gamma gamma' A hAright hAleft)
            hfg hfExclusive hsource)


theorem
    rlc_twoChannelFullPhysical_contactCycle_BChanging_sourceBoundary_or_targetBad_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ f g : Site 2,
      s(f, g) ∈ c.edges ∧
        rlc_dualReflect f ∈
          rlc_twoChannelFullPhysicalLiftVertexCut B ∧
        rlc_dualReflect g ∉
          rlc_twoChannelFullPhysicalLiftVertexCut B ∧
        ((∃ p q : Site 2,
          sharedPrimalEdge f g = s(p, q) ∧
            (hypercubicLattice 2).Adj p q ∧
            p ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) ∧
            q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) ∧
            (p ∈ rlc_connectorBarrier gamma gamma' ∨
              p 0 = -2 * n ∨ p 0 = 2 * n ∨
              p 1 = -n ∨ p 1 = n) ∧
            ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
              gamma gamma' f g) ∨
          ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
            gamma gamma' f g) := by
  obtain ⟨f, g, hfgCycle, hfB, hgB, hbad⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_BChanging_not_planar_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
        c hx hy hxPath hyPath
  have hfgBoundary : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj f g :=
    c.adj_of_mem_edges hfgCycle
  refine ⟨f, g, hfgCycle, hfB, hgB, ?_⟩
  rcases hbad with hsourceBad | htargetBad
  · left
    obtain ⟨p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace⟩ :=
      rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
          hfgBoundary hsourceBad
    exact ⟨p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace, fun hsource ↦
      hsourceBad
        (rlc_twoChannelFullPhysical_sourceCarrier_planar
          gamma gamma' hsource)⟩
  · right
    intro htarget
    have hcentral :=
      rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier
        gamma gamma' hfgBoundary htarget
    exact htargetBad
      ((rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
        gamma gamma' hfgBoundary.1).1 hcentral)


theorem
    rlc_twoChannelFullPhysical_contactCycle_BChanging_exactCarrierFailure_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ f g : Site 2,
      s(f, g) ∈ c.edges ∧
        rlc_dualReflect f ∈
          rlc_twoChannelFullPhysicalLiftVertexCut B ∧
        rlc_dualReflect g ∉
          rlc_twoChannelFullPhysicalLiftVertexCut B ∧
        (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
            gamma gamma' f g ∨
          ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
            gamma gamma' f g) := by
  obtain ⟨f, g, hfgCycle, hfB, hgB, hsource | htarget⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_BChanging_sourceBoundary_or_targetBad_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
        c hx hy hxPath hyPath
  · obtain ⟨_p, _q, _hpq, _hpqAdj, _hpReach, _hqOut,
        _hpPlace, hsourceBad⟩ := hsource
    exact ⟨f, g, hfgCycle, hfB, hgB, Or.inl hsourceBad⟩
  · exact ⟨f, g, hfgCycle, hfB, hgB, Or.inr htarget⟩


theorem
    rlc_twoChannelFullPhysical_contactCycle_BChanging_exactNoncarrier_of_noPair
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ f g : Site 2,
      s(f, g) ∈ c.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' f g := by
  obtain ⟨f, g, hfgCycle, hfB, hgB, hsourceBad | htargetBad⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_BChanging_exactCarrierFailure_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
        c hx hy hxPath hyPath
  all_goals
    refine ⟨f, g, hfgCycle,
      ⟨rlc_dualReflect f, rlc_dualReflect g, rfl,
        Or.inl ⟨hfB, hgB⟩⟩, ?_⟩
  · intro hcarrier
    exact hsourceBad
      ((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
        gamma gamma' f g).1 hcarrier).2
  · intro hcarrier
    exact htargetBad
      ((rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source
        gamma gamma' f g).1 hcarrier).1


theorem rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' f g) :
    (¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∨
      sharedPrimalEdge f g ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  rcases (rlc_twoChannelFullPhysical_not_carrierGeometry_iff
    gamma gamma' f g).1 hbad with htarget | hsource
  · exact Or.inl htarget
  · exact Or.inr (rlc_twoChannelFullPhysical_sourceBad_not_planar
      gamma gamma' omega hfg hsource)


theorem rlc_twoChannelFullPhysical_boundary_insideSourceWitness
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
  obtain ⟨a, b, hab, habAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hbd := hfg.2
  rw [hab, bdEdge_mk] at hbd
  by_cases ha : a ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega
  · have hb : b ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega :=
      hbd.mp ha
    exact ⟨a, b, hab, habAdj,
      rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
        gamma gamma' omega ha hb habAdj, hb⟩
  · have hb : b ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
      by_contra hb
      exact ha (hbd.mpr hb)
    exact ⟨b, a, by simpa [Sym2.eq_swap] using hab, habAdj.symm,
      rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
        gamma gamma' omega hb ha habAdj.symm, ha⟩


theorem rlc_twoChannelFullPhysical_boundary_insideSourceWalk
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g f' g' : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hfg' : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f' g') :
    ∃ (p q p' q' : Site 2)
      (w : (hypercubicLattice 2).Walk p p'),
      sharedPrimalEdge f g = s(p, q) ∧
        sharedPrimalEdge f' g' = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        ∀ z ∈ w.support,
          z ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
            z ∈ rect (-2 * n) (2 * n) (-n) n := by
  obtain ⟨p, q, hpq, hpqAdj, hpReach, hqOut⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWitness
      gamma gamma' omega hfg
  obtain ⟨p', q', hpq', hpqAdj', hpReach', hqOut'⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWitness
      gamma gamma' omega hfg'
  obtain ⟨wind⟩ := rlc_twoChannelFullReachSet_reachable
    gamma gamma' omega hpReach hpReach'
  let hom : ((hypercubicLattice 2).induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)) →g
      hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce
      (G := hypercubicLattice 2)
      (rlc_twoChannelFullReachSet gamma gamma' omega)).toHom
  let w : (hypercubicLattice 2).Walk p p' := wind.map hom
  refine ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
    hpReach', hqOut, hqOut', ?_⟩
  intro z hz
  change z ∈ (wind.map hom).support at hz
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  exact ⟨v.2, rlc_twoChannelFullReachSet_subset_box
    gamma gamma' omega v.2⟩


theorem rlc_twoChannelFullAmbientConfig_open_source_or_originalTrace
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {e : Sym2 (Site 2)}
    (hopen : rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true) :
    (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val = e) ∨
      e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  classical
  unfold rlc_twoChannelFullAmbientConfig at hopen
  split at hopen
  · rename_i hsource
    exact Or.inl ⟨hsource.some.1, hsource.some.2⟩
  · rename_i hsource
    split at hopen
    · rename_i htrace
      exact Or.inr htrace
    · simp at hopen


theorem rlc_twoChannelFullPhysical_boundary_insideOpenSourceWalk
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g f' g' : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hfg' : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f' g') :
    ∃ (p q p' q' : Site 2)
      (w : (hypercubicLattice 2).Walk p p'),
      sharedPrimalEdge f g = s(p, q) ∧
        sharedPrimalEdge f' g' = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (∀ z ∈ w.support,
          z ∈ rlc_twoChannelFullReachSet gamma gamma' omega) ∧
        ∀ e ∈ w.edges,
          rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true := by
  obtain ⟨p, q, hpq, hpqAdj, hpReach, hqOut⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWitness
      gamma gamma' omega hfg
  obtain ⟨p', q', hpq', hpqAdj', hpReach', hqOut'⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWitness
      gamma gamma' omega hfg'
  have hpReach0 := hpReach
  have hpReach0' := hpReach'
  obtain ⟨hpBox, hpConnected⟩ := hpReach
  obtain ⟨hp'Box, hp'Connected⟩ := hpReach'
  obtain ⟨wp⟩ := hpConnected
  obtain ⟨wp'⟩ := hp'Connected
  let sourceGraph := openSubgraphInduce 2
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
      (rect (-2 * n) (2 * n) (-n) n)
  let hom : sourceGraph →g hypercubicLattice 2 := {
    toFun := fun z ↦ z.1
    map_rel' := fun {_ _} h ↦ h.1 }
  let ww := wp.reverse.append wp'
  let w := ww.map hom
  refine ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach0,
    hpReach0', hqOut, hqOut', ?_, ?_⟩
  · intro z hz
    change z ∈ (ww.map hom).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    dsimp only [ww] at ha
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at ha
    rcases ha with ha | ha
    · refine ⟨a.2, ?_⟩
      exact ⟨wp.takeUntil a (by simpa using ha)⟩
    · refine ⟨a.2, ?_⟩
      exact ⟨wp'.takeUntil a ha⟩
  · intro e he
    change e ∈ (ww.map hom).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    induction e₀ using Sym2.inductionOn with
    | _ a b =>
        have hab := ww.adj_of_mem_edges he₀
        exact hab.2


theorem rlc_flankFaces_eq_of_sharedPrimalEdge_eq
    {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q)) :
    flankFaces p q = s(f, g) := by
  calc
    flankFaces p q = flankFacesSym s(p, q) := by
      rw [flankFacesSym_mk]
    _ = flankFacesSym (sharedPrimalEdge f g) :=
      congrArg flankFacesSym hshared.symm
    _ = flankFacesSym (symPrimal f g) := by
      rw [symPrimal_eq_shared hfg]
    _ = s(f, g) := flankFacesSym_symPrimal hfg


theorem rlc_doubleDualShift_endpoint_mem_boundaryEdge
    {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hshared : sharedPrimalEdge f g = s(p, q)) :
    phb_doubleDualShift p ∈ s(f, g) ∨
      phb_doubleDualShift q ∈ s(f, g) := by
  have hmem := rlc_doubleDualShift_endpoint_mem_flankFaces hpq
  rwa [rlc_flankFaces_eq_of_sharedPrimalEdge_eq hfg hshared] at hmem


theorem rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry
    {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q)) :
    (g = ![f 0 + 1, f 1] ∧
        ((phb_doubleDualShift p = f ∧
            phb_doubleDualShift q = ![f 0, f 1 - 1]) ∨
          (phb_doubleDualShift p = ![f 0, f 1 - 1] ∧
            phb_doubleDualShift q = f))) ∨
      (g = ![f 0 - 1, f 1] ∧
        ((phb_doubleDualShift p = g ∧
            phb_doubleDualShift q = ![f 0 - 1, f 1 - 1]) ∨
          (phb_doubleDualShift p = ![f 0 - 1, f 1 - 1] ∧
            phb_doubleDualShift q = g))) ∨
      (g = ![f 0, f 1 + 1] ∧
        ((phb_doubleDualShift p = f ∧
            phb_doubleDualShift q = ![f 0 - 1, f 1]) ∨
          (phb_doubleDualShift p = ![f 0 - 1, f 1] ∧
            phb_doubleDualShift q = f))) ∨
      (g = ![f 0, f 1 - 1] ∧
        ((phb_doubleDualShift p = g ∧
            phb_doubleDualShift q = ![f 0 - 1, f 1 - 1]) ∨
          (phb_doubleDualShift p = ![f 0 - 1, f 1 - 1] ∧
            phb_doubleDualShift q = g))) := by
  rcases face_adj_dir hfg with hg | hg | hg | hg
  · left
    refine ⟨hg, ?_⟩
    subst g
    rw [show sharedPrimalEdge f ![f 0 + 1, f 1] =
        s(![f 0 + 1, f 1], ![f 0 + 1, f 1 + 1]) by
          simpa using sharedPrimalEdge_right (f 0) (f 1),
      Sym2.eq_iff] at hshared
    rcases hshared with h | h <;> rcases h with ⟨rfl, rfl⟩
    · right
      constructor <;> ext i <;> fin_cases i <;>
        simp [phb_doubleDualShift]
    · left
      constructor <;> ext i <;> fin_cases i <;>
        simp [phb_doubleDualShift]
  · right; left
    refine ⟨hg, ?_⟩
    subst g
    rw [show sharedPrimalEdge f ![f 0 - 1, f 1] =
        s(faceCorner00 (f 0) (f 1), faceCorner01 (f 0) (f 1)) by
          simpa using sharedPrimalEdge_left (f 0) (f 1),
      Sym2.eq_iff] at hshared
    rcases hshared with h | h <;> rcases h with ⟨rfl, rfl⟩
    · right
      constructor <;> ext i <;> fin_cases i <;>
        simp [phb_doubleDualShift, faceCorner00, faceCorner01]
    · left
      constructor <;> ext i <;> fin_cases i <;>
        simp [phb_doubleDualShift, faceCorner00, faceCorner01]
  · right; right; left
    refine ⟨hg, ?_⟩
    subst g
    rw [show sharedPrimalEdge f ![f 0, f 1 + 1] =
        s(![f 0, f 1 + 1], ![f 0 + 1, f 1 + 1]) by
          simpa using sharedPrimalEdge_top (f 0) (f 1),
      Sym2.eq_iff] at hshared
    rcases hshared with h | h <;> rcases h with ⟨rfl, rfl⟩
    · right
      constructor <;> ext i <;> fin_cases i <;>
        simp [phb_doubleDualShift]
    · left
      constructor <;> ext i <;> fin_cases i <;>
        simp [phb_doubleDualShift]
  · right; right; right
    refine ⟨hg, ?_⟩
    subst g
    rw [show sharedPrimalEdge f ![f 0, f 1 - 1] =
        s(faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1)) by
          simpa using sharedPrimalEdge_bottom (f 0) (f 1),
      Sym2.eq_iff] at hshared
    rcases hshared with h | h <;> rcases h with ⟨rfl, rfl⟩
    · right
      constructor <;> ext i <;> fin_cases i <;>
        simp [phb_doubleDualShift, faceCorner00, faceCorner10]
    · left
      constructor <;> ext i <;> fin_cases i <;>
        simp [phb_doubleDualShift, faceCorner00, faceCorner10]


theorem rlc_sharedPrimalEdge_endpoint_horizontal_bounds
    {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q)) :
    f 0 ≤ p 0 ∧ p 0 ≤ f 0 + 1 ∧
      f 0 ≤ q 0 ∧ q 0 ≤ f 0 + 1 := by
  have hgeom :=
    rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry hfg hshared
  rcases hgeom with ⟨hdir, hord⟩ | ⟨hdir, hord⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, hord⟩ <;>
    rcases hord with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;>
    have hp0 := congrArg (fun z : Site 2 => z 0) hp <;>
    have hq0 := congrArg (fun z : Site 2 => z 0) hq <;>
    simp only [phb_doubleDualShift, Matrix.cons_val_zero] at hp0 hq0 <;>
    (try simp only [hdir, Matrix.cons_val_zero] at hp0 hq0) <;>
    omega


theorem rlc_walk_secondFace_to_doubleDualShift_firstEndpoint
    {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q)) :
    ∃ P : (hypercubicLattice 2).Walk g (phb_doubleDualShift p),
      ∀ z ∈ P.support,
        z = g ∨ z = f ∨ z = phb_doubleDualShift p := by
  have hgeom :=
    rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry hfg hshared
  rcases hgeom with ⟨hdir, hord⟩ | ⟨hdir, hord⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, hord⟩
  · rcases hord with ⟨hp, _hq⟩ | ⟨hp, _hq⟩
    · rw [hp]
      exact ⟨.cons hfg.symm .nil, by simp⟩
    · have hdrop : (hypercubicLattice 2).Adj f ![f 0, f 1 - 1] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      rw [hp]
      exact ⟨.cons hfg.symm (.cons hdrop .nil), by simp⟩
  · rcases hord with ⟨hp, _hq⟩ | ⟨hp, _hq⟩
    · rw [hp]
      exact ⟨.nil, by simp⟩
    · have hdrop : (hypercubicLattice 2).Adj g ![f 0 - 1, f 1 - 1] := by
        rw [hdir]
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      rw [hp]
      exact ⟨.cons hdrop .nil, by simp⟩
  · rcases hord with ⟨hp, _hq⟩ | ⟨hp, _hq⟩
    · rw [hp]
      exact ⟨.cons hfg.symm .nil, by simp⟩
    · have hdrop : (hypercubicLattice 2).Adj f ![f 0 - 1, f 1] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      rw [hp]
      exact ⟨.cons hfg.symm (.cons hdrop .nil), by simp⟩
  · rcases hord with ⟨hp, _hq⟩ | ⟨hp, _hq⟩
    · rw [hp]
      exact ⟨.nil, by simp⟩
    · have hdrop : (hypercubicLattice 2).Adj g ![f 0 - 1, f 1 - 1] := by
        rw [hdir]
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      rw [hp]
      exact ⟨.cons hdrop .nil, by simp⟩


theorem rlc_walk_secondFace_to_doubleDualShift_firstEndpoint_with_incidence
    {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q)) :
    ∃ P : (hypercubicLattice 2).Walk g (phb_doubleDualShift p),
      (∀ z ∈ P.support,
        z = g ∨ z = f ∨ z = phb_doubleDualShift p) ∧
      (phb_doubleDualShift q ∈ s(f, g) →
        phb_doubleDualShift q ∈ P.support) := by
  have hgeom :=
    rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry hfg hshared
  rcases hgeom with ⟨hdir, hord⟩ | ⟨hdir, hord⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, hord⟩
  · rcases hord with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [hp]
      refine ⟨.cons hfg.symm .nil, by simp, ?_⟩
      intro hinc
      rw [hq, hdir, Sym2.mem_iff] at hinc
      rcases hinc with h | h <;> simp_all
    · have hdrop : (hypercubicLattice 2).Adj f ![f 0, f 1 - 1] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      rw [hp]
      refine ⟨.cons hfg.symm (.cons hdrop .nil), by simp, ?_⟩
      intro _hinc
      rw [hq]
      simp
  · rcases hord with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [hp]
      refine ⟨.nil, by simp, ?_⟩
      intro hinc
      rw [hq, hdir, Sym2.mem_iff] at hinc
      rcases hinc with h | h <;> simp_all
    · have hdrop : (hypercubicLattice 2).Adj g ![f 0 - 1, f 1 - 1] := by
        rw [hdir]
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      rw [hp]
      refine ⟨.cons hdrop .nil, by simp, ?_⟩
      intro _hinc
      rw [hq]
      simp
  · rcases hord with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [hp]
      refine ⟨.cons hfg.symm .nil, by simp, ?_⟩
      intro hinc
      rw [hq, hdir, Sym2.mem_iff] at hinc
      rcases hinc with h | h <;> simp_all
    · have hdrop : (hypercubicLattice 2).Adj f ![f 0 - 1, f 1] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      rw [hp]
      refine ⟨.cons hfg.symm (.cons hdrop .nil), by simp, ?_⟩
      intro _hinc
      rw [hq]
      simp
  · rcases hord with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [hp]
      refine ⟨.nil, by simp, ?_⟩
      intro hinc
      rw [hq, hdir, Sym2.mem_iff] at hinc
      rcases hinc with h | h <;> simp_all
    · have hdrop : (hypercubicLattice 2).Adj g ![f 0 - 1, f 1 - 1] := by
        rw [hdir]
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      rw [hp]
      refine ⟨.cons hdrop .nil, by simp, ?_⟩
      intro _hinc
      rw [hq]
      simp


theorem rlc_doubleDualShiftWalk_between_boundaryEdges
    {p q p' q' f g f' g' : Site 2}
    (w : (hypercubicLattice 2).Walk p p')
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hstart : phb_doubleDualShift p ∈ s(f, g) ∨
      phb_doubleDualShift q ∈ s(f, g))
    (hend : phb_doubleDualShift p' ∈ s(f', g') ∨
      phb_doubleDualShift q' ∈ s(f', g')) :
    ∃ (a b : Site 2) (W : (hypercubicLattice 2).Walk a b),
      a ∈ s(f, g) ∧ b ∈ s(f', g') ∧
        (a = phb_doubleDualShift p ∨ a = phb_doubleDualShift q) ∧
        (b = phb_doubleDualShift p' ∨ b = phb_doubleDualShift q') ∧
        ∀ z ∈ W.support,
          z = phb_doubleDualShift q ∨
            z = phb_doubleDualShift q' ∨
            ∃ v ∈ w.support, phb_doubleDualShift v = z := by
  let hom : hypercubicLattice 2 →g hypercubicLattice 2 := {
    toFun := phb_doubleDualShift
    map_rel' := fun {_ _} h ↦ phb_doubleDualShift_latAdj.mpr h }
  let W₀ := w.map hom
  have hW₀ {z : Site 2} (hz : z ∈ W₀.support) :
      ∃ v ∈ w.support, phb_doubleDualShift v = z := by
    change z ∈ (w.map hom).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact ⟨v, hv, rfl⟩
  have hpqShift : (hypercubicLattice 2).Adj
      (phb_doubleDualShift p) (phb_doubleDualShift q) :=
    phb_doubleDualShift_latAdj.mpr hpq
  have hpqShift' : (hypercubicLattice 2).Adj
      (phb_doubleDualShift p') (phb_doubleDualShift q') :=
    phb_doubleDualShift_latAdj.mpr hpq'
  rcases hstart with hpStart | hqStart <;>
    rcases hend with hpEnd | hqEnd
  · exact ⟨phb_doubleDualShift p, phb_doubleDualShift p', W₀,
      hpStart, hpEnd, Or.inl rfl, Or.inl rfl,
      fun z hz ↦ Or.inr (Or.inr (hW₀ hz))⟩
  · let post : (hypercubicLattice 2).Walk
        (phb_doubleDualShift p') (phb_doubleDualShift q') :=
      .cons hpqShift' .nil
    let W := W₀.append post
    refine ⟨phb_doubleDualShift p, phb_doubleDualShift q', W,
      hpStart, hqEnd, Or.inl rfl, Or.inr rfl, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact Or.inr (Or.inr (hW₀ hz))
    · simp [post] at hz
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inr (hW₀ W₀.end_mem_support))
      · exact Or.inr (Or.inl rfl)
  · let pre : (hypercubicLattice 2).Walk
        (phb_doubleDualShift q) (phb_doubleDualShift p) :=
      .cons hpqShift.symm .nil
    let W := pre.append W₀
    refine ⟨phb_doubleDualShift q, phb_doubleDualShift p', W,
      hqStart, hpEnd, Or.inr rfl, Or.inl rfl, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · simp [pre] at hz
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hW₀ W₀.start_mem_support))
    · exact Or.inr (Or.inr (hW₀ hz))
  · let pre : (hypercubicLattice 2).Walk
        (phb_doubleDualShift q) (phb_doubleDualShift p) :=
      .cons hpqShift.symm .nil
    let post : (hypercubicLattice 2).Walk
        (phb_doubleDualShift p') (phb_doubleDualShift q') :=
      .cons hpqShift' .nil
    let W := (pre.append W₀).append post
    refine ⟨phb_doubleDualShift q, phb_doubleDualShift q', W,
      hqStart, hqEnd, Or.inr rfl, Or.inr rfl, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · simp [pre] at hz
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hW₀ W₀.start_mem_support))
    · exact Or.inr (Or.inr (hW₀ hz))
    · simp [post] at hz
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inr (hW₀ W₀.end_mem_support))
      · exact Or.inr (Or.inl rfl)


theorem rlc_doubleDualShift_mem_translatedRect
    {alpha beta bottom top : Int} {p : Site 2}
    (hp : p ∈ rect alpha beta bottom top) :
    phb_doubleDualShift p ∈
      rect (alpha - 1) (beta - 1) (bottom - 1) (top - 1) := by
  rw [mem_rect] at hp ⊢
  simp only [phb_doubleDualShift, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  omega


theorem rlc_doubleDualShift_neighbor_mem_expandedRect
    {alpha beta bottom top : Int} {p q : Site 2}
    (hp : p ∈ rect alpha beta bottom top)
    (hpq : (hypercubicLattice 2).Adj p q) :
    phb_doubleDualShift q ∈
      rect (alpha - 2) beta (bottom - 2) top := by
  rw [mem_rect] at hp ⊢
  rcases adj_cases hpq with
      ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩ <;>
    simp only [phb_doubleDualShift, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    omega


theorem rlc_orientedBoundaryWitness_unique
    {H : Set (Site 2)} {p q r s : Site 2}
    (hp : p ∈ H) (hs : s ∉ H)
    (heq : s(p, q) = s(r, s)) : p = r ∧ q = s := by
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨hpr, hqs⟩ | ⟨hps, hqr⟩
  · exact ⟨hpr, hqs⟩
  · exact False.elim (hs (hps ▸ hp))


theorem rlc_walk_between_tethers
    {a b t u : Site 2} (W : (hypercubicLattice 2).Walk a b)
    (ha : a = t ∨ (hypercubicLattice 2).Adj a t)
    (hb : b = u ∨ (hypercubicLattice 2).Adj b u) :
    ∃ W' : (hypercubicLattice 2).Walk t u,
      ∀ z ∈ W'.support, z = t ∨ z = u ∨ z ∈ W.support := by
  rcases ha with rfl | hat <;> rcases hb with rfl | hbu
  · exact ⟨W, fun z hz ↦ Or.inr (Or.inr hz)⟩
  · let post : (hypercubicLattice 2).Walk b u := .cons hbu .nil
    let W' := W.append post
    refine ⟨W', ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact Or.inr (Or.inr hz)
    · simp [post] at hz
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inr W.end_mem_support)
      · exact Or.inr (Or.inl rfl)
  · let pre : (hypercubicLattice 2).Walk t a := .cons hat.symm .nil
    let W' := pre.append W
    refine ⟨W', ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · simp [pre] at hz
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr W.start_mem_support)
    · exact Or.inr (Or.inr hz)
  · let pre : (hypercubicLattice 2).Walk t a := .cons hat.symm .nil
    let post : (hypercubicLattice 2).Walk b u := .cons hbu .nil
    let W' := (pre.append W).append post
    refine ⟨W', ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · simp [pre] at hz
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr W.start_mem_support)
    · exact Or.inr (Or.inr hz)
    · simp [post] at hz
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inr W.end_mem_support)
      · exact Or.inr (Or.inl rfl)


theorem rlc_neighbor_mem_expandedRect
    {alpha beta bottom top : Int} {p q : Site 2}
    (hp : p ∈ rect alpha beta bottom top)
    (hpq : (hypercubicLattice 2).Adj p q) :
    q ∈ rect (alpha - 1) (beta + 1) (bottom - 1) (top + 1) := by
  rw [mem_rect] at hp ⊢
  rcases adj_cases hpq with
      ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩ <;> omega


end
end StatMech.Universality
