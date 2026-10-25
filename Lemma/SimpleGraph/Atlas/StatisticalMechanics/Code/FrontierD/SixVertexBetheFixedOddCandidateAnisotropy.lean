import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddCandidateAnisotropy.Part4
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexThetaLeftDerivAtZero_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexThetaLeftDerivAtZero_atTop_eq
-- given
  (y : Real -> Real) :
-- imply
  Tendsto (fun c => sixVertexThetaLeftDerivAtZero c (y c)) atTop (nhds (-1)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexThetaLeftDerivAtZero_atTop y

/--
[sixVertexFixedOddCentralLimitingRoot_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean)
-/
@[path]
private lemma sixVertexFixedOddCentralLimitingRoot_eq_zero_eq
  {s k : Nat} :
-- imply
  sixVertexFixedChargeLimitingRoot (2 * s + 1) k (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddCentralLimitingRoot_eq_zero s k

/--
[sixVertexFixedOddCentralLimitingPhase_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean)
-/
@[path]
private lemma sixVertexFixedOddCentralLimitingPhase_eq_one_eq
  {s k : Nat} :
-- imply
  sixVertexFixedChargeLimitingPhase (2 * s + 1) k (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddCentralLimitingPhase_eq_one s k

/--
[sixVertexFixedOddLimitingPhase_ne_one_of_ne_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean)
-/
@[path]
private lemma sixVertexFixedOddLimitingPhase_ne_one_of_ne_central_eq
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hj : j ≠ sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) :
-- imply
  sixVertexFixedChargeLimitingPhase (2 * s + 1) k j ≠ 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddLimitingPhase_ne_one_of_ne_central s k j hj

/--
[tendsto_sixVertexFixedOddChargeBethePrefactorNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedOddChargeBethePrefactorNormalized_eq
  {s k : Nat} :
-- imply
  Tendsto (sixVertexFixedOddChargeBethePrefactorNormalized s k) atTop (nhds (sixVertexFixedChargeBetheComplementCount (2 * s + 1) k)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedOddChargeBethePrefactorNormalized s k

/--
[tendsto_sixVertexFixedOddChargeNormalizedMProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedOddChargeNormalizedMProduct_eq
  {s k : Nat} :
-- imply
  Tendsto (sixVertexFixedOddChargeNormalizedMProduct s k) atTop (nhds (sixVertexFixedOddChargeLimitingMProduct s k)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedOddChargeNormalizedMProduct s k

/--
[tendsto_sixVertexFixedOddChargeBetheCandidateNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedOddChargeBetheCandidateNormalized_eq
  {s k : Nat} :
-- imply
  Tendsto (sixVertexFixedOddChargeBetheCandidateNormalized s k) atTop (nhds (sixVertexFixedOddChargeBetheCandidateInfinity s k)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedOddChargeBetheCandidateNormalized s k


-- created on 2026-10-23
