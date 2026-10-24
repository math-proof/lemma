import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeEventualPerron
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexFixedChargeRotatedNormalizedWave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeRotatedNormalizedWave_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  Tendsto (fun c => sixVertexFixedChargeRotatedNormalizedWave r k c x) atTop (nhds (sixVertexFixedChargeRotatedLimitingWave r k x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeRotatedNormalizedWave r k x

/--
[eventually_sixVertexFixedEvenChargeRotatedNormalizedWave_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma eventually_sixVertexFixedEvenChargeRotatedNormalizedWave_eigenrelation_eq
  {s k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) c *ᵥ sixVertexFixedChargeRotatedNormalizedWave (2 * s) k c = sixVertexFixedEvenChargeBetheCandidateNormalized s k c • sixVertexFixedChargeRotatedNormalizedWave (2 * s) k c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedEvenChargeRotatedNormalizedWave_eigenrelation s k

/--
[eventually_sixVertexFixedOddChargeRotatedNormalizedWave_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma eventually_sixVertexFixedOddChargeRotatedNormalizedWave_eigenrelation_eq
  {s k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) c *ᵥ sixVertexFixedChargeRotatedNormalizedWave (2 * s + 1) k c = sixVertexFixedOddChargeBetheCandidateNormalized s k c • sixVertexFixedChargeRotatedNormalizedWave (2 * s + 1) k c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedOddChargeRotatedNormalizedWave_eigenrelation s k

/--
[sixVertexFixedEvenChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent_eq
  {s k : Nat}
  {x : SixVertexSector (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hx : ¬ SixVertexSectorNoAdjacent x) :
-- imply
  sixVertexFixedChargeRotatedLimitingWave (2 * s) k x = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent s k x hx

/--
[sixVertexFixedOddChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent_eq
  {s k : Nat}
  {x : SixVertexSector (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hx : ¬ SixVertexSectorNoAdjacent x) :
-- imply
  sixVertexFixedChargeRotatedLimitingWave (2 * s + 1) k x = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent s k x hx

/--
[eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_eq_top_eq
  {s k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, sixVertexFixedEvenChargeBetheCandidateNormalized s k c = sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (by have := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k omega) c / (c ^ 2 - 2) ^ sixVertexFixedChargeBetheParticleCount (2 * s) k := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_eq_top s k

/--
[eventually_sixVertexFixedOddChargeBetheCandidateNormalized_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma eventually_sixVertexFixedOddChargeBetheCandidateNormalized_eq_top_eq
  {s k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, sixVertexFixedOddChargeBetheCandidateNormalized s k c = sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (by have := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k omega) c / (c ^ 2 - 2) ^ sixVertexFixedChargeBetheParticleCount (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedOddChargeBetheCandidateNormalized_eq_top s k

/--
[eventually_sixVertexFixedEvenChargeBetheCandidate_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma eventually_sixVertexFixedEvenChargeBetheCandidate_eq_top_eq
  {s k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, forall hc : 2 < c, sixVertexFixedEvenChargeBetheEigenvalueValue hc s k = sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (by have := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k omega) c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedEvenChargeBetheCandidate_eq_top s k

/--
[eventually_sixVertexFixedOddChargeBetheCandidate_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean)
-/
@[path]
private lemma eventually_sixVertexFixedOddChargeBetheCandidate_eq_top_eq
  {s k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, forall hc : 2 < c, sixVertexFixedOddChargeBetheEigenvalueValue hc (2 * s + 1) k = sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (by have := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k omega) c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedOddChargeBetheCandidate_eq_top s k


-- created on 2026-10-23
