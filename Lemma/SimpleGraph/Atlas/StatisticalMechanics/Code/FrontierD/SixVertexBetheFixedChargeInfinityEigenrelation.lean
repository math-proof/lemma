import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityEigenrelation
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeCoordinateBetheWave_eq_scale_mul_normalizedWave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityEigenrelation.lean)
-/
@[path]
private lemma sixVertexFixedChargeCoordinateBetheWave_eq_scale_mul_normalizedWave_eq
  {c : Real}
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k) x = sixVertexFixedChargePairScaleProduct r k c * sixVertexFixedChargeNormalizedWave r k c x := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeCoordinateBetheWave_eq_scale_mul_normalizedWave hc r k x

/--
[sixVertexFixedChargeNormalizedWave_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityEigenrelation.lean)
-/
@[path]
private lemma sixVertexFixedChargeNormalizedWave_eigenrelation_eq
  {c μ : Real}
  {r k : Nat}
-- given
  (hc : 2 < c)
  (hrelation : (sixVertexSectorTransferComplex (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) c).mulVec (sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k)) = (μ : Complex) • sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k)) :
-- imply
  ∀ x, ∑ y, ((sixVertexSectorTransferNormalized (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) : Complex) * sixVertexFixedChargeNormalizedWave r k c y = ((μ / (c ^ 2 - 2) ^ sixVertexFixedChargeBetheParticleCount r k : Real) : Complex) * sixVertexFixedChargeNormalizedWave r k c x := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeNormalizedWave_eigenrelation hc r k hrelation

/--
[sixVertexFixedEvenChargeLimitingWave_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityEigenrelation.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeLimitingWave_eigenrelation_eq
  {s k : Nat} :
-- imply
  ∀ x, ∑ y, sixVertexSectorTransferInfinity (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) x y * sixVertexFixedChargeLimitingWave (2 * s) k y = (sixVertexFixedEvenChargeBetheCandidateInfinity s k : Complex) * sixVertexFixedChargeLimitingWave (2 * s) k x := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeLimitingWave_eigenrelation s k

/--
[sixVertexFixedOddChargeLimitingWave_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityEigenrelation.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeLimitingWave_eigenrelation_eq
  {s k : Nat} :
-- imply
  ∀ x, ∑ y, sixVertexSectorTransferInfinity (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) x y * sixVertexFixedChargeLimitingWave (2 * s + 1) k y = (sixVertexFixedOddChargeBetheCandidateInfinity s k : Complex) * sixVertexFixedChargeLimitingWave (2 * s + 1) k x := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeLimitingWave_eigenrelation s k


-- created on 2026-10-23
