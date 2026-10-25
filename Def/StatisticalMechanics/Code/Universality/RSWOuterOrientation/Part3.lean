/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Structure.StatisticalMechanics.Code.Universality.RSWOuterOrientation.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcOuterContourContactOrder.toOriented {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : RlcOuterContourContactOrder G omega) :
    RlcOrientedContourContactOrder G omega where
  anchor := rlc_outerExitAnchor G omega
  rightContact := h.rightContact
  leftContact := h.leftContact
  right_mem := h.right_mem
  left_mem := h.left_mem
  right_trace := h.right_trace
  left_trace := h.left_trace
  supportedSide := h.supportedSide


noncomputable def rlc_outerExitReflectedOpenLoop {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega))).Walk
      (rlc_dualReflect (dartFace (rlc_outerExitAnchor G omega).1))
      (rlc_dualReflect (dartFace (rlc_outerExitAnchor G omega).1)) :=
  rlc_dualReflectOpenWalk
    (rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega)
    ((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)).mapLe
        (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))


def RlcOuterExitContactArcOrder {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∀ {x y : Site 2}
    (hx : x ∈ (mpl_orbitFaceLoop
      (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)).support)
    (hy : y ∈ (mpl_orbitFaceLoop
      (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)).support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
    RlcContourArcRelaxedLocalSide G omega
      (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)) hx hy


end Universality
end StatMech
