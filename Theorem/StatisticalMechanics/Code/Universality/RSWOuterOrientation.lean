/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Structure.StatisticalMechanics.Code.Universality.RSWOuterOrientation
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOrientedContourContactOrder G omega) :
    RlcTraceContactsCutOffRelaxedBadEdges G omega
      (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) h.anchor) := by
  let c := mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) h.anchor
  refine ⟨h.rightContact, h.leftContact, h.right_mem, h.left_mem,
    h.right_trace, h.left_trace, ?_⟩
  rcases h.supportedSide with hordered | hcomplementary
  · left
    intro f g hedge hbad
    rcases (rlc_contourArc_edges_cover
      c h.right_mem h.left_mem).mp hedge with hord | hcomp
    · exact False.elim (hbad (hordered hord))
    · exact hcomp
  · right
    intro f g hedge hbad
    rcases (rlc_contourArc_edges_cover
      c h.right_mem h.left_mem).mp hedge with hord | hcomp
    · exact hord
    · exact False.elim (hbad (hcomplementary hcomp))


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerContourContactOrder
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOrientedContourContactOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide
    G hn hlt omega
    (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) h.anchor)
    h.right_mem h.left_mem h.right_trace h.left_trace h.supportedSide


end Universality
end StatMech
