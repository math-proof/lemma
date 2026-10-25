/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_boundaryContactArc_of_walkContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {f g : Site 2}
    (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk f g)
    (hcontacts : RlcCentralFaceWalkContactSegment gamma gamma' rho a) :
    RlcCentralFaceBoundaryContactArc gamma gamma' rho := by
  obtain ⟨x, y, hx, hy, hxPath, hyPath, htarget⟩ := hcontacts
  exact ⟨x, y, rlc_centralFaceContactSubwalk a hx hy,
    hxPath, hyPath, htarget⟩


theorem rlc_centralFacePIMS_openWalk_of_reflected_walk {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {x y : Site 2}
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho))).Walk x y)
    (hy : y ∈ rlc_pathVertices gamma'.1)
    (htarget : ∀ e ∈ c.edges,
      e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma') :
    ∃ (hxBox : x ∈ rect (-2 * n) (2 * n) (-n) n)
      (hyBox : y ∈ rect (-2 * n) (2 * n) (-n) n),
      Nonempty ((FK.openSub
        (rlc_connectorCentralFaceClosureGraph gamma gamma')
        (rlc_connectorCentralFacePIMSConfig gamma gamma' rho)).Walk
          ⟨x, hxBox⟩ ⟨y, hyBox⟩) := by
  have hyBox : y ∈ rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' hy
  have hsupp : ∀ z ∈ c.support,
      z ∈ rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · exact hyBox
    · simpa [rlc_connectorBox] using
        rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
          gamma gamma' (htarget e he) hze
  let cbox := c.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hsupp
  refine ⟨hsupp x c.start_mem_support, hyBox, ⟨cbox.transfer
    (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
      (rlc_connectorCentralFacePIMSConfig gamma gamma' rho)) ?_⟩⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      let hom := (SimpleGraph.Embedding.induce
        (G := openSubgraph 2 (rlc_dualReflectConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)))
        (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
      have hec : s((u : Site 2), (v : Site 2)) ∈ c.edges := by
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) cbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom cbox] at hmap
        simpa [hom, cbox] using hmap
      have hadj := c.adj_of_mem_edges hec
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      refine ⟨⟨hadj.1, htarget _ hec⟩, ?_⟩
      simpa [rlc_connectorCentralFacePIMSConfig,
        rlc_connectorRestrictConfig, Sym2.map_mk] using hadj.2


theorem rlc_centralFacePIMS_success_of_boundaryContactArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcCentralFaceBoundaryContactArc gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  obtain ⟨x, y, a, hx, hy, htarget⟩ := harc
  let eta := rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
  let hle := rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho
  let c := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  obtain ⟨hxBox, hyBox, cfinite⟩ :=
    rlc_centralFacePIMS_openWalk_of_reflected_walk gamma gamma' rho c hy htarget
  exact ⟨⟨rlc_dualReflect x, hxBox⟩, ⟨rlc_dualReflect y, hyBox⟩,
    hx, hy, cfinite.some.reachable⟩

end
end StatMech.Universality
