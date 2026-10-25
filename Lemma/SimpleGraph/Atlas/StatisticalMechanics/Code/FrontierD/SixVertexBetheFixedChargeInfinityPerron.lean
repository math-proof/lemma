import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityPerron
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexFixedChargePositiveInfinityWave_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPerron.lean)
-/
@[path]
private lemma sixVertexFixedChargePositiveInfinityWave_pos_eq
  {r k : Nat}
  {x : SixVertexNoAdjacentSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  0 < sixVertexFixedChargePositiveInfinityWave r k x := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargePositiveInfinityWave_pos r k x

/--
[sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPerron.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron_eq
  {s k : Nat} :
-- imply
  sixVertexFixedEvenChargeBetheCandidateInfinity s k = sixVertexNoAdjacentInfinityTopEigenvalue (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheParticleCount_pos (2 * s) k) (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron s k

/--
[sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPerron.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron_eq
  {s k : Nat} :
-- imply
  sixVertexFixedOddChargeBetheCandidateInfinity s k = sixVertexNoAdjacentInfinityTopEigenvalue (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount_pos (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron s k


-- created on 2026-10-23
