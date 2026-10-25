/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part3
import Def.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcStoppedExtremalAxisGapProvenance.toExtremalPairCandidate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt) :
    (rlc_extremalPairCandidate (gamma, gamma')).Nonempty :=
  S.selectedStratum


theorem RlcStoppedExtremalAxisGapProvenance.toFailureSelectedSideTopology
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt) :
    RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt :=
  rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector
    G hn hlt S.anchoredSelector


theorem RlcStoppedExtremalAxisGapProvenance.boundaryArc_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
  exact rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists G hn hlt tau
    (S.toFailureSelectedSideTopology tau hno)


theorem RlcStoppedExtremalAxisGapProvenance.pims_success_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  rlc_axisGapPIMS_success_of_anchoredContourSelector
    G hn hlt S.anchoredSelector tau hno


end
end StatMech.Universality
