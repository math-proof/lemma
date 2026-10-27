import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
open StatMech StatMech.Universality


/--
[rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStaticCutEndpoint.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_retainedAnchor_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1) :
-- imply
  RlcTwoChannelPIMSPooledVisibleFibreCapacity (rlc_twoChannelClosureFailureCertificate_of_centralFace gamma gamma' (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence hinc)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_retainedAnchor_staticCut hinc hstatic

/--
[rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStaticCutEndpoint.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_retainedAnchor_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 <= q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_retainedAnchor_staticCut hinc hstatic hq N hscore

/--
[rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStaticCutEndpoint.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_retainedAnchor_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1) :
-- imply
  (1 / 2 : Real) <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint 1) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_retainedAnchor_staticCut hinc hstatic


-- created on 2026-10-23
