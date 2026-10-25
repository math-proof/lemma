/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part86
import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedPathOrientation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcStoppedTwoChannelOrientedCommonCycleState.candidateState
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (hz : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
    RlcStoppedTwoChannelOrientedCandidateStateAt X z :=
  ⟨hz, X.candidate_obstruction z hz⟩


theorem
    RlcStoppedTwoChannelOrientedCommonCycleState.candidateTransition
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hbracket : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    (rlc_dualReflect x = z ∧
        rlc_dualReflect y = rlc_flipX z) ∨
      (∃ q,
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
          RlcStoppedTwoChannelOrientedCandidateStateAt X q) ∨
      ∃ q,
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
          RlcStoppedTwoChannelOrientedCandidateStateAt X q := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition
        hzCandidate hyPath hflipLeftRank hbracket with
    hfixed | ⟨q, hqCandidate, hqz⟩ | ⟨q, hqCandidate, hzq⟩
  · exact Or.inl hfixed
  · exact Or.inr (Or.inl ⟨q, hqz, X.candidateState hqCandidate⟩)
  · exact Or.inr (Or.inr ⟨q, hzq, X.candidateState hqCandidate⟩)


theorem RlcStoppedTwoChannelOrientedCommonCycleState.boundaryArc_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau :=
  X.provenance.boundaryArc_of_failure tau hno


theorem RlcStoppedTwoChannelOrientedCommonCycleState.pims_success_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  X.provenance.pims_success_of_failure tau hno


theorem RlcStoppedTwoChannelOrientedCandidateStateAt.boundaryArc_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (_hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau :=
  X.boundaryArc_of_failure tau hno


theorem RlcStoppedTwoChannelOrientedCandidateStateAt.pims_success_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (_hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  X.pims_success_of_failure tau hno


end
end StatMech.Universality
