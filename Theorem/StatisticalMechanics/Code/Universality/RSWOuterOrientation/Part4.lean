/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Def.StatisticalMechanics.Code.Universality.RSWOuterOrientation.Part3
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_outerExit_traceContactsCutOffRelaxedBadEdges_of_straddles
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hright : rlc_TraceStraddlesLoop
      ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma.1)
    (hleft : rlc_TraceStraddlesLoop
      ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma'.1)
    (horder : RlcOuterExitContactArcOrder G omega) :
    RlcTraceContactsCutOffRelaxedBadEdges G omega
      (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)) := by
  let c := mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
    (rlc_outerExitAnchor G omega)
  let q := rlc_outerExitReflectedOpenLoop G hn hlt omega
  obtain ⟨⟨xr, hxrPath, hxrQ⟩, ⟨yr, hyrPath, hyrQ⟩⟩ :=
    rlc_reflectedOpenDualCycle_contacts_both_of_straddles
      q gamma gamma' hright hleft
  have hqSupport : q.support = List.map rlc_dualReflect c.support := by
    simp [q, c, rlc_outerExitReflectedOpenLoop,
      rlc_dualReflectOpenWalk, SimpleGraph.Walk.support_map,
      SimpleGraph.Walk.support_mapLe_eq_support, rlc_dualReflectOpenHom]
  rw [hqSupport] at hxrQ hyrQ
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hxrQ
  obtain ⟨y, hy, hyr⟩ := List.mem_map.mp hyrQ
  have hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
    simpa using hxr ▸ hxrPath
  have hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
    simpa using hyr ▸ hyrPath
  let hdata : RlcOuterContourContactOrder G omega := {
    rightContact := x
    leftContact := y
    right_mem := hx
    left_mem := hy
    right_trace := hxPath
    left_trace := hyPath
    supportedSide := horder hx hy hxPath hyPath }
  exact rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder
    G omega hdata.toOriented


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerExit_straddles
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hright : rlc_TraceStraddlesLoop
      ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma.1)
    (hleft : rlc_TraceStraddlesLoop
      ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
        (rlc_openSubgraph_le_lattice _)) gamma'.1)
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, y, hx, hy, hxPath, hyPath, _hplace⟩ :=
    rlc_outerExit_traceContactsCutOffRelaxedBadEdges_of_straddles
      G hn hlt omega hright hleft horder
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide
    G hn hlt omega
    (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega))
    hx hy hxPath hyPath (horder hx hy hxPath hyPath)


theorem rlc_traceContactsCutOffRelaxedBadEdges_of_outerExitContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOuterContourContactOrder G omega) :
    RlcTraceContactsCutOffRelaxedBadEdges G omega
      (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)) :=
  rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder
    G omega h.toOriented


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOuterContourContactOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G :=
  rlc_mixedWiredConnectorEvent_dualReflect_of_outerContourContactOrder
    G hn hlt omega h.toOriented

end Universality
end StatMech
