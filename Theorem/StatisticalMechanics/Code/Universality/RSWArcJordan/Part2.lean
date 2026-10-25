/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWOuterArc
import Theorem.StatisticalMechanics.Code.Universality.RSWTraceContact.Part4
import Def.StatisticalMechanics.Code.Universality.RSWArcJordan
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcLocalSide
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hside : RlcContourArcLocalSide G omega c hx hy) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  apply rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcSide
    G hn hlt omega c hx hy hxPath hyPath
  rcases hside with hforward | hbackward
  · left
    refine ⟨?_, hforward⟩
    exact rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal
      G (rlc_orderedContourArc c hx hy) hyPath (fun he => (hforward he).1)
  · right
    refine ⟨?_, hbackward⟩
    exact rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal
      G (rlc_complementaryContourArc c hx hy) hyPath
        (fun he => (hbackward he).1)


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_straddles_of_arcLocalSide
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hright : rlc_TraceStraddlesLoop
      ((rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma.1)
    (hleft : rlc_TraceStraddlesLoop
      ((rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma'.1)
    (hJordan : ∀ {x y : Site 2}
      (hx : x ∈ c.support) (hy : y ∈ c.support),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
      RlcContourArcLocalSide G omega c hx hy) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega
  let q := rlc_dualReflectOpenWalk eta (c.mapLe hle)
  obtain ⟨⟨xr, hxrPath, hxrQ⟩, ⟨yr, hyrPath, hyrQ⟩⟩ :=
    rlc_reflectedOpenDualCycle_contacts_both_of_straddles
      q gamma gamma' hright hleft
  have hqSupport : q.support = List.map rlc_dualReflect c.support := by
    simp [q, rlc_dualReflectOpenWalk, SimpleGraph.Walk.support_map,
      SimpleGraph.Walk.support_mapLe_eq_support, rlc_dualReflectOpenHom]
  rw [hqSupport] at hxrQ hyrQ
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hxrQ
  obtain ⟨y, hy, hyr⟩ := List.mem_map.mp hyrQ
  have hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
    simpa using hxr ▸ hxrPath
  have hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
    simpa using hyr ▸ hyrPath
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcLocalSide
    G hn hlt omega c hx hy hxPath hyPath
      (hJordan hx hy hxPath hyPath)

end Universality
end StatMech
