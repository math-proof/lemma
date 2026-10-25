/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcAxisGapPIMSAnchoredContourCore {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) where
  lowerAxis : Site 2
  upperAxis : Site 2
  firstFace : Site 2
  secondFace : Site 2
  baseFace : Site 2
  contour : (faceBoundaryGraph
    (rlc_axisGapReachSet G (rlc_axisGapAmbientConfig G tau))).Walk
      baseFace baseFace
  axis_boundary : (lowerAxis, upperAxis) ∈ edgeBoundary 2
    (rlc_axisGapReachSet G (rlc_axisGapAmbientConfig G tau))
  lowerAxis_zero : lowerAxis 0 = 0
  upperAxis_zero : upperAxis 0 = 0
  anchor_adj : (faceBoundaryGraph
    (rlc_axisGapReachSet G (rlc_axisGapAmbientConfig G tau))).Adj
      firstFace secondFace
  anchor_shared : sharedPrimalEdge firstFace secondFace =
    s(lowerAxis, upperAxis)
  contour_isCycle : contour.IsCycle
  anchor_mem : s(firstFace, secondFace) ∈ contour.edges


end
end StatMech.Universality
