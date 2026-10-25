/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcAxisGapPIMSAnchoredSelectedSide {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (C : RlcAxisGapPIMSAnchoredContourCore G tau) where
  rightContact : Site 2
  leftContact : Site 2
  right_mem : rightContact ∈ C.contour.support
  left_mem : leftContact ∈ C.contour.support
  right_trace : rlc_dualReflect rightContact ∈
    rlc_pathVertices gamma.1
  left_trace : rlc_dualReflect leftContact ∈
    rlc_pathVertices gamma'.1
  supportedSide :
    let eta := rlc_maskConfig (rlc_axisGapEdges G)
      (rlc_axisGapAmbientConfig G tau)
    let hle := rlc_axisGapFaceBoundaryGraph_le_openFaceDual
      G hn hlt (rlc_axisGapAmbientConfig G tau)
    (∀ e ∈ (rlc_dualReflectOpenWalk eta
      ((rlc_orderedContourArc C.contour right_mem left_mem).mapLe hle)).edges,
      e ∈ rlc_axisGapEdges G) ∨
    ∀ e ∈ (rlc_dualReflectOpenWalk eta
      ((rlc_complementaryContourArc C.contour
        right_mem left_mem).mapLe hle)).edges,
      e ∈ rlc_axisGapEdges G


end
end StatMech.Universality
