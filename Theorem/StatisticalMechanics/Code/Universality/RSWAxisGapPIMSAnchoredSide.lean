/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part3
import Structure.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_axisGapPIMSAnchoredContourCore_of_failure {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    Nonempty (RlcAxisGapPIMSAnchoredContourCore G tau) := by
  have hamb : rlc_axisGapAmbientConfig G tau ∉
      rlc_axisGapConnectorEvent G := by
    intro hconn
    exact hno
      ((rlc_axisGapAmbientConfig_mem_connectorEvent_iff G tau).mp hconn)
  obtain ⟨p, q, f, g, u, c, hpq, hp0, hq0, hfg,
      hshared, hcycle, hedge⟩ :=
    rlc_axisGapReachSet_axis_anchored_dualCircuit
      G (rlc_axisGapAmbientConfig G tau) hamb
  exact ⟨{
    lowerAxis := p
    upperAxis := q
    firstFace := f
    secondFace := g
    baseFace := u
    contour := c
    axis_boundary := hpq
    lowerAxis_zero := hp0
    upperAxis_zero := hq0
    anchor_adj := hfg
    anchor_shared := hshared
    contour_isCycle := hcycle
    anchor_mem := hedge
  }⟩


end
end StatMech.Universality
