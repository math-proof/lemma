import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelPooledVisibleEmbeddingOfCapacity_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean)
-/
@[path]
private lemma rlc_twoChannelPooledVisibleEmbeddingOfCapacity_compatible_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'}
-- given
  (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure) :
-- imply
  RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho (rlc_twoChannelPooledVisibleEmbeddingOfCapacity hcapacity rho) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPooledVisibleEmbeddingOfCapacity_compatible hcapacity rho

/--
[rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_exists_compatibleEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_exists_compatibleEmbedding_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔ ∃ J : RlcTwoChannelEdgeFailure gamma gamma' ↪ RlcTwoChannelEdgeSuccess gamma gamma', forall rho, RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho (J rho) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_exists_compatibleEmbedding hclosure

/--
[rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_edgeCodeHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_edgeCodeHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔ RlcTwoChannelEdgeCodeHall gamma gamma' (RlcTwoChannelPIMSPooledVisibleCompatible hclosure) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_edgeCodeHall hclosure

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_pooledVisibleCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_pooledVisibleCapacity_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_pooledVisibleCapacity gamma gamma' hclosure hcapacity

/--
[rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_pooledScoreHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_pooledScoreHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hq : 1 <= q)
  (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' (RlcTwoChannelPIMSPooledScoreCompatible hclosure N)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= (Real.sqrt q) ^ N * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_pooledScoreHall gamma gamma' hclosure hq N hHall

/--
[rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_pooledScoreHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_pooledScoreHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hq : 1 <= q)
  (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' (RlcTwoChannelPIMSPooledScoreCompatible hclosure N)) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_pooledScoreHall gamma gamma' hclosure hq N hHall


-- created on 2026-10-23
