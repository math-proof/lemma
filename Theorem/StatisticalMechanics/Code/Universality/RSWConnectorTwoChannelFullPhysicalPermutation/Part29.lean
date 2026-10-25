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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part29
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj f g)
    (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f))
    (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g)) :
    RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure
      gamma gamma' B f g := by
  rcases
      rlc_twoChannelFullPhysical_BChanging_terminalClassification_of_noPair
        gamma gamma' A B hAright hAleft hnoPair hfg hcross with
    htarget | hsource
  · exact Or.inl ⟨htarget,
      rlc_twoChannelFullPhysical_targetBad_not_reflectedLeft_of_exclusive
        gamma gamma' hfg hfExclusive htarget⟩
  · exact Or.inr hsource


theorem
    rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_traceCross
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {p q : Site 2}
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n)
    (hpExclusive :
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' p)
    (hqBox : q ∈ rlc_connectorBox n)
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
    (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      s(p, q) = false) :
    s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
      ∃ z : Site 2,
        (hypercubicLattice 2).Adj p z ∧
          rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s(p, z) = true ∧
          (s(p, z) ∈ rlc_reflectedPathEdges gamma.1 ∨
            (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧
              z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧
              ∀ y : Site 2,
                (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
                  s(p, y) ∈ rlc_reflectedPathEdges gamma.1)) := by
  have hpFlipLeft : ¬ ∃ w ∈ rlc_pathVertices gamma'.1,
      p = rlc_flipX w := by
    rintro ⟨w, hw, hpw⟩
    have hwBox := rlc_pathVertex_mem_rect gamma'.1 hw
    rw [mem_rect] at hwBox
    have hpNeg := hpExclusive.1
    rw [hpw] at hpNeg
    simp [rlc_flipX, rlc_flipXFun] at hpNeg
    omega
  have reflectedRight_of_wall {y : Site 2}
      (hyWall : s(p, y) ∈
        rlc_connectorFourTraceEdges gamma gamma') :
      s(p, y) ∈ rlc_reflectedPathEdges gamma.1 :=
    rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
      gamma gamma' hyWall (Sym2.mem_mk_left _ _)
        hpExclusive.2.2.1 hpExclusive.2.2.2 hpFlipLeft
  rcases
      rlc_twoChannelFullPhysical_reachable_interior_edge_planar_or_last_wall_or_opposite
        gamma gamma' omega hpReach hpInterior hqBox hpqAdj hpAnchor
          hpqClosed with
    hplanar | ⟨z, hpzAdj, hpzOpen, hpzPlace⟩
  · exact Or.inl hplanar
  · by_cases hpzWall : s(p, z) ∈
        rlc_connectorFourTraceEdges gamma gamma'
    · exact Or.inr ⟨z, hpzAdj, hpzOpen,
        Or.inl (reflectedRight_of_wall hpzWall)⟩
    · have hpzOpposite : z 0 + q 0 = 2 * p 0 ∧
          z 1 + q 1 = 2 * p 1 :=
        hpzPlace.resolve_left hpzWall
      by_cases hallSides : ∀ y : Site 2,
          (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
            s(p, y) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · exact Or.inr ⟨z, hpzAdj, hpzOpen, Or.inr
          ⟨hpzWall, hpzOpposite.1, hpzOpposite.2,
            fun y hy hyz hyq => reflectedRight_of_wall
              (hallSides y hy hyz hyq)⟩⟩
      · push Not at hallSides
        obtain ⟨y, hpyAdj, hyz, hyq, hpyWall⟩ := hallSides
        have hpzPlanar :=
          rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
            gamma gamma' omega hpzOpen
        rw [rlc_mem_connectorCentralFacePlanarEdges_iff
          gamma gamma' hpzAdj] at hpzPlanar
        rcases hpzPlanar with hpzWall' |
            ⟨_hpBox, _hzBox, h, hhRegion, hhFlank⟩
        · exact False.elim (hpzWall hpzWall')
        · left
          apply rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
            gamma gamma' hpzAdj hpqAdj hpInterior hpzWall
              hhRegion hhFlank
          refine ⟨y, hpyAdj, hyz, hyq, ?_, ?_, hpyWall⟩
          · intro hzy
            apply hyq
            funext i
            fin_cases i
            · change y 0 = q 0
              omega
            · change y 1 = q 1
              omega
          · intro hyqOpposite
            apply hyz
            funext i
            fin_cases i
            · change y 0 = z 0
              omega
            · change y 1 = z 1
              omega


theorem
    rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_traceCross
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {p q : Site 2}
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n)
    (hpExclusive :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' p)
    (hqBox : q ∈ rlc_connectorBox n)
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
    (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      s(p, q) = false) :
    s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
      ∃ z : Site 2,
        (hypercubicLattice 2).Adj p z ∧
          rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s(p, z) = true ∧
          (s(p, z) ∈ rlc_reflectedPathEdges gamma'.1 ∨
            (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧
              z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧
              ∀ y : Site 2,
                (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
                  s(p, y) ∈ rlc_reflectedPathEdges gamma'.1)) := by
  have hpFlipRight : ¬ ∃ w ∈ rlc_pathVertices gamma.1,
      p = rlc_flipX w := by
    rintro ⟨w, hw, hpw⟩
    have hwBox := rlc_pathVertex_mem_rect gamma.1 hw
    rw [mem_rect] at hwBox
    have hpPos := hpExclusive.1
    rw [hpw] at hpPos
    simp [rlc_flipX, rlc_flipXFun] at hpPos
    omega
  have reflectedLeft_of_wall {y : Site 2}
      (hyWall : s(p, y) ∈
        rlc_connectorFourTraceEdges gamma gamma') :
      s(p, y) ∈ rlc_reflectedPathEdges gamma'.1 :=
    rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
      gamma gamma' hyWall (Sym2.mem_mk_left _ _)
        hpExclusive.2.2.1 hpExclusive.2.2.2 hpFlipRight
  rcases
      rlc_twoChannelFullPhysical_reachable_interior_edge_planar_or_last_wall_or_opposite
        gamma gamma' omega hpReach hpInterior hqBox hpqAdj hpAnchor
          hpqClosed with
    hplanar | ⟨z, hpzAdj, hpzOpen, hpzPlace⟩
  · exact Or.inl hplanar
  · by_cases hpzWall : s(p, z) ∈
        rlc_connectorFourTraceEdges gamma gamma'
    · exact Or.inr ⟨z, hpzAdj, hpzOpen,
        Or.inl (reflectedLeft_of_wall hpzWall)⟩
    · have hpzOpposite : z 0 + q 0 = 2 * p 0 ∧
          z 1 + q 1 = 2 * p 1 :=
        hpzPlace.resolve_left hpzWall
      by_cases hallSides : ∀ y : Site 2,
          (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
            s(p, y) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · exact Or.inr ⟨z, hpzAdj, hpzOpen, Or.inr
          ⟨hpzWall, hpzOpposite.1, hpzOpposite.2,
            fun y hy hyz hyq => reflectedLeft_of_wall
              (hallSides y hy hyz hyq)⟩⟩
      · push Not at hallSides
        obtain ⟨y, hpyAdj, hyz, hyq, hpyWall⟩ := hallSides
        have hpzPlanar :=
          rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
            gamma gamma' omega hpzOpen
        rw [rlc_mem_connectorCentralFacePlanarEdges_iff
          gamma gamma' hpzAdj] at hpzPlanar
        rcases hpzPlanar with hpzWall' |
            ⟨_hpBox, _hzBox, h, hhRegion, hhFlank⟩
        · exact False.elim (hpzWall hpzWall')
        · left
          apply rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
            gamma gamma' hpzAdj hpqAdj hpInterior hpzWall
              hhRegion hhFlank
          refine ⟨y, hpyAdj, hyz, hyq, ?_, ?_, hpyWall⟩
          · intro hzy
            apply hyq
            funext i
            fin_cases i
            · change y 0 = q 0
              omega
            · change y 1 = q 1
              omega
          · intro hyqOpposite
            apply hyz
            funext i
            fin_cases i
            · change y 0 = z 0
              omega
            · change y 1 = z 1
              omega


theorem
    rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_sourceTraceCross
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {p q : Site 2}
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n)
    (hpExclusive :
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' p)
    (hqBox : q ∈ rlc_connectorBox n)
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
    (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      s(p, q) = false) :
    s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
      ∃ z : Site 2,
        (hypercubicLattice 2).Adj p z ∧
          rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s(p, z) = true ∧
          ((∃ source :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
              source.1.map Subtype.val = s(p, z)) ∨
            (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧
              z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧
              ∀ y : Site 2,
                (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
                  ∃ source :
                    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
                    source.1.map Subtype.val = s(p, y))) := by
  rcases
      rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_traceCross
        gamma gamma' omega hpReach hpInterior hpExclusive hqBox hpqAdj
          hpAnchor hpqClosed with
    hplanar | ⟨z, hpzAdj, hpzOpen, hpzTrace | hpzCross⟩
  · exact Or.inl hplanar
  · exact Or.inr ⟨z, hpzAdj, hpzOpen, Or.inl
      (rlc_twoChannelFullPhysical_exclusiveReflectedRightEdge_sourceWitness
        gamma gamma' hpExclusive hpzAdj hpzTrace)⟩
  · refine Or.inr ⟨z, hpzAdj, hpzOpen, Or.inr
      ⟨hpzCross.1, hpzCross.2.1, hpzCross.2.2.1, ?_⟩⟩
    intro y hpyAdj hyz hyq
    exact
      rlc_twoChannelFullPhysical_exclusiveReflectedRightEdge_sourceWitness
        gamma gamma' hpExclusive hpyAdj
          (hpzCross.2.2.2 y hpyAdj hyz hyq)


theorem
    rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_sourceTraceCross
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {p q : Site 2}
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n)
    (hpExclusive :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' p)
    (hqBox : q ∈ rlc_connectorBox n)
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
    (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      s(p, q) = false) :
    s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨
      ∃ z : Site 2,
        (hypercubicLattice 2).Adj p z ∧
          rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s(p, z) = true ∧
          ((∃ source :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
              source.1.map Subtype.val = s(p, z)) ∨
            (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧
              z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧
              ∀ y : Site 2,
                (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
                  ∃ source :
                    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
                    source.1.map Subtype.val = s(p, y))) := by
  rcases
      rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_traceCross
        gamma gamma' omega hpReach hpInterior hpExclusive hqBox hpqAdj
          hpAnchor hpqClosed with
    hplanar | ⟨z, hpzAdj, hpzOpen, hpzTrace | hpzCross⟩
  · exact Or.inl hplanar
  · exact Or.inr ⟨z, hpzAdj, hpzOpen, Or.inl
      (rlc_twoChannelFullPhysical_exclusiveReflectedLeftEdge_sourceWitness
        gamma gamma' hpExclusive hpzAdj hpzTrace)⟩
  · refine Or.inr ⟨z, hpzAdj, hpzOpen, Or.inr
      ⟨hpzCross.1, hpzCross.2.1, hpzCross.2.2.1, ?_⟩⟩
    intro y hpyAdj hyz hyq
    exact
      rlc_twoChannelFullPhysical_exclusiveReflectedLeftEdge_sourceWitness
        gamma gamma' hpExclusive hpyAdj
          (hpzCross.2.2.2 y hpyAdj hyz hyq)


theorem rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hbad : sharedPrimalEdge f g ∉
      rlc_connectorCentralFacePlanarEdges gamma gamma') :
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (p ∈ rlc_connectorBarrier gamma gamma' ∨
          p 0 = -2 * n ∨ p 0 = 2 * n ∨
          p 1 = -n ∨ p 1 = n) := by
  obtain ⟨a, b, hab, habAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hbd := hfg.2
  rw [hab, bdEdge_mk] at hbd
  have localize {p q : Site 2}
      (hpq : sharedPrimalEdge f g = s(p, q))
      (hpqAdj : (hypercubicLattice 2).Adj p q)
      (hpFilled : p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
      (hqFilled : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
      p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        (p ∈ rlc_connectorBarrier gamma gamma' ∨
          p 0 = -2 * n ∨ p 0 = 2 * n ∨
          p 1 = -n ∨ p 1 = n) := by
    have hpReach := rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hpFilled hqFilled hpqAdj
    refine ⟨hpReach, ?_⟩
    obtain ⟨hpBox, hpConnected⟩ := hpReach
    by_cases hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
        -n < p 1 ∧ p 1 < n
    · left
      by_contra hpBarrier
      obtain ⟨w⟩ := hpConnected
      cases w.reverse with
      | nil =>
          exact hpBarrier (by
            simp [rlc_connectorRightAnchor, rlc_connectorBarrier,
              rlc_path_start_mem_vertices gamma.1])
      | @cons _ z _ hpz tail =>
          have hpzOpen : rlc_twoChannelFullAmbientConfig gamma gamma' omega
              s(p, (z : Site 2)) = true := by
            rw [openSubgraphInduce_adj, openSubgraph_adj] at hpz
            exact hpz.2
          have hpzPlanar :=
            rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
              gamma gamma' omega hpzOpen
          have hpzAdj : (hypercubicLattice 2).Adj p (z : Site 2) := by
            rw [openSubgraphInduce_adj, openSubgraph_adj] at hpz
            exact hpz.1
          rw [rlc_mem_connectorCentralFacePlanarEdges_iff
            gamma gamma' hpzAdj] at hpzPlanar
          rcases hpzPlanar with hpzWall |
              ⟨hpConnectorBox, _hzConnectorBox, h, hhRegion, hhFlank⟩
          · exact hpBarrier
              (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
                gamma gamma' hpzWall (Sym2.mem_mk_left _ _))
          · have hqConnectorBox : q ∈ rlc_connectorBox n := by
              simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
              rw [mem_rect]
              rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqAdj
              omega
            generalize hkEq : flankFaces p q = e
            induction e using Sym2.inductionOn with
            | _ k l =>
                have hkFlank : k ∈ flankFaces p q := by
                  rw [hkEq]
                  exact Sym2.mem_mk_left _ _
                have hkRegion := rlc_centralFaceRegion_flank_transfer_interior
                  gamma gamma' hpzAdj hpqAdj hpInterior hpBarrier
                    hhRegion hhFlank hkFlank
                apply hbad
                rw [hpq]
                exact rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
                  gamma gamma' hpqAdj hpConnectorBox hqConnectorBox
                    hkRegion hkFlank
    · right
      rw [mem_rect] at hpBox
      push Not at hpInterior
      omega
  by_cases haFilled :
      a ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega
  · have hbFilled :
        b ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega :=
      hbd.mp haFilled
    obtain ⟨haReach, haPlace⟩ :=
      localize hab habAdj haFilled hbFilled
    exact ⟨a, b, hab, habAdj, haReach, hbFilled, haPlace⟩
  · have hbFilled :
        b ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
      tauto
    have hba : sharedPrimalEdge f g = s(b, a) := by
      simpa [Sym2.eq_swap] using hab
    obtain ⟨hbReach, hbPlace⟩ :=
      localize hba habAdj.symm hbFilled haFilled
    exact ⟨b, a, hba, habAdj.symm, hbReach, haFilled, hbPlace⟩


end
end StatMech.Universality
