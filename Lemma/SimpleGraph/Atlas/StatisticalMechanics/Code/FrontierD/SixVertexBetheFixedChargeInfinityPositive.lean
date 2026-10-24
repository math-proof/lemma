import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityPositive
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeLimitingWave_eq_phase_mul_sineProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPositive.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingWave_eq_phase_mul_sineProduct_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  sixVertexFixedChargeLimitingWave r k x = Complex.I ^ sixVertexFixedChargeBethePairCount r k * sixVertexFixedChargeLimitingSineProduct r k x := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingWave_eq_phase_mul_sineProduct r k x

/--
[sixVertexFixedChargeLimitingSineProduct_pos_of_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPositive.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingSineProduct_pos_of_noAdjacent_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  0 < sixVertexFixedChargeLimitingSineProduct r k x := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingSineProduct_pos_of_noAdjacent r k x hx

/--
[sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPositive.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  0 < ((-Complex.I) ^ sixVertexFixedChargeBethePairCount r k * sixVertexFixedChargeLimitingWave r k x).re := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent r k x hx


-- created on 2026-10-23
