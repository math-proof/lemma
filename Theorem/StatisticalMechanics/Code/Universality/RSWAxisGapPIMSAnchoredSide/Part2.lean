/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part3
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_axisGapPIMSBoundaryArc_of_anchoredSelectedSide {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {C : RlcAxisGapPIMSAnchoredContourCore G tau}
    (hside : RlcAxisGapPIMSAnchoredSelectedSide G hn hlt tau C) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
  rcases hside.supportedSide with hforward | hbackward
  · exact ⟨hside.rightContact, hside.leftContact,
      rlc_orderedContourArc C.contour hside.right_mem hside.left_mem,
      hside.right_trace, hside.left_trace, hforward⟩
  · exact ⟨hside.rightContact, hside.leftContact,
      rlc_complementaryContourArc C.contour
        hside.right_mem hside.left_mem,
      hside.right_trace, hside.left_trace, hbackward⟩


theorem rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hside : RlcAxisGapPIMSAnchoredSideExists G hn hlt tau) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
  obtain ⟨C, hC⟩ := hside
  obtain ⟨hselected⟩ := hC
  exact rlc_axisGapPIMSBoundaryArc_of_anchoredSelectedSide
    G hn hlt tau hselected


end
end StatMech.Universality
