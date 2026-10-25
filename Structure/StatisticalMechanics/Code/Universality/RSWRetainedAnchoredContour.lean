/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWFailureSelectedCarryObstruction
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


structure RlcRetainedFailureAnchoredContour {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) where
  height : ℤ
  firstFace : Site 2
  secondFace : Site 2
  baseFace : Site 2
  contour : (faceBoundaryGraph
    (rlc_mixedWiredReachSet G omega)).Walk baseFace baseFace
  height_lower : G.lower ≤ height
  height_upper : height < G.upper
  axis_inside : ![0, height] ∈ rlc_mixedWiredReachSet G omega
  axis_outside : ![0, height + 1] ∉ rlc_mixedWiredReachSet G omega
  anchor_adj : (faceBoundaryGraph
    (rlc_mixedWiredReachSet G omega)).Adj firstFace secondFace
  anchor_shared : sharedPrimalEdge firstFace secondFace =
    s(![0, height], ![0, height + 1])
  contour_isCycle : contour.IsCycle
  anchor_mem : s(firstFace, secondFace) ∈ contour.edges
  carries_contact_arc :
    RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega contour


end Universality
end StatMech
