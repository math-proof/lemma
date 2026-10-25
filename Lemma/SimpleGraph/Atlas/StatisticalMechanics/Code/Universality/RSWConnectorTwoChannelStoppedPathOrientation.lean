import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedPathOrientation.Part2
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[RlcStoppedTwoChannelOrientedCommonCycleState.candidateState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma candidateState_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
-- imply
  RlcStoppedTwoChannelOrientedCandidateStateAt X z := by
-- proof
  apply StatMech.Universality.RlcStoppedTwoChannelOrientedCommonCycleState.candidateState X hz

/--
[RlcStoppedTwoChannelOrientedCommonCycleState.candidateTransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma candidateTransition_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hbracket : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  (rlc_dualReflect x = z ∧ rlc_dualReflect y = rlc_flipX z) ∨ (∃ q, (rlc_ambientCrossingWalk gamma.1).support.idxOf q < (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧ RlcStoppedTwoChannelOrientedCandidateStateAt X q) ∨ ∃ q, (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧ RlcStoppedTwoChannelOrientedCandidateStateAt X q := by
-- proof
  apply StatMech.Universality.RlcStoppedTwoChannelOrientedCommonCycleState.candidateTransition X hzCandidate hyPath hflipLeftRank hbracket

/--
[RlcStoppedTwoChannelOrientedCommonCycleState.boundaryArc_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma boundaryArc_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
-- proof
  apply StatMech.Universality.RlcStoppedTwoChannelOrientedCommonCycleState.boundaryArc_of_failure X tau hno

/--
[RlcStoppedTwoChannelOrientedCommonCycleState.pims_success_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma pims_success_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.RlcStoppedTwoChannelOrientedCommonCycleState.pims_success_of_failure X tau hno

/--
[RlcStoppedTwoChannelOrientedCandidateStateAt.boundaryArc_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma boundaryArc_of_failure_eq_2
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega}
  {z : Site 2}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (_hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
-- proof
  apply StatMech.Universality.RlcStoppedTwoChannelOrientedCandidateStateAt.boundaryArc_of_failure X _hz tau hno

/--
[RlcStoppedTwoChannelOrientedCandidateStateAt.pims_success_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma pims_success_of_failure_eq_2
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega}
  {z : Site 2}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (_hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.RlcStoppedTwoChannelOrientedCandidateStateAt.pims_success_of_failure X _hz tau hno

/--
[RlcStoppedTwoChannelOrientedCandidateStateAt.resolved_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma resolved_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega}
  {z : Site 2}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  RlcStoppedTwoChannelCandidateResolved (G := G) omega tau := by
-- proof
  apply StatMech.Universality.RlcStoppedTwoChannelOrientedCandidateStateAt.resolved_of_failure X hz tau hno

/--
[RlcStoppedTwoChannelOrientedCommonCycleState.no_unresolved_candidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma no_unresolved_candidate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega}
  {z : Site 2}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  ¬(¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∧ rlc_axisGapPIMSReflectedConfig G tau ∉ rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.RlcStoppedTwoChannelOrientedCommonCycleState.no_unresolved_candidate X hz tau hno

/--
[rlc_stoppedTwoChannel_good_or_pimsSuccess_of_failures](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean)
-/
@[path]
private lemma rlc_stoppedTwoChannel_good_or_pimsSuccess_of_failures_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {S : RlcStoppedExtremalAxisGapProvenance G hn hlt}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoTwoChannel : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGap : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  RlcStoppedTwoChannelCandidateResolved (G := G) omega tau := by
-- proof
  apply StatMech.Universality.rlc_stoppedTwoChannel_good_or_pimsSuccess_of_failures G hn hlt S hfaith omega hnoTwoChannel tau hnoGap


-- created on 2026-10-23
