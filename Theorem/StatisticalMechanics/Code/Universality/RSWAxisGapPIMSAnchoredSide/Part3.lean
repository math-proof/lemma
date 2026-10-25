/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part3
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (hselector : RlcAxisGapPIMSAnchoredContourSelector G hn hlt) :
    RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt := by
  intro tau hno
  obtain ⟨C⟩ := rlc_axisGapPIMSAnchoredContourCore_of_failure G tau hno
  exact ⟨C, hselector tau hno C⟩


theorem rlc_axisGapPIMS_success_of_failureSelectedSideTopology {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (htopology : RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G := by
  apply rlc_axisGapPIMSReflectedConfig_mem_event_of_boundaryArc
    G hn hlt tau
  exact rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists
    G hn hlt tau (htopology tau hno)


theorem rlc_axisGapPIMS_success_of_anchoredContourSelector {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (hselector : RlcAxisGapPIMSAnchoredContourSelector G hn hlt)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  rlc_axisGapPIMS_success_of_failureSelectedSideTopology G hn hlt
    (rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector
      G hn hlt hselector) tau hno

end
end StatMech.Universality
