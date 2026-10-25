import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityNonzero
open Finset Matrix StatMech StatMech.FrontierD


/--
[strictMono_sixVertexFixedChargeAlternantExponent_of_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityNonzero.lean)
-/
@[path]
private lemma strictMono_sixVertexFixedChargeAlternantExponent_of_noAdjacent_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  StrictMono (sixVertexFixedChargeAlternantExponent r k x) := by
-- proof
  apply StatMech.FrontierD.strictMono_sixVertexFixedChargeAlternantExponent_of_noAdjacent r k x hx

/--
[sixVertexFixedChargeAlternantExponent_sub_abs_lt_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityNonzero.lean)
-/
@[path]
private lemma sixVertexFixedChargeAlternantExponent_sub_abs_lt_complement_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
  {i j : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  abs ((sixVertexFixedChargeAlternantExponent r k x i : Real) - sixVertexFixedChargeAlternantExponent r k x j) < sixVertexFixedChargeBetheComplementCount r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeAlternantExponent_sub_abs_lt_complement r k x hx i j

/--
[sixVertexFixedChargeAlternantPoint_injective_of_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityNonzero.lean)
-/
@[path]
private lemma sixVertexFixedChargeAlternantPoint_injective_of_noAdjacent_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  Function.Injective (sixVertexFixedChargeAlternantPoint r k x) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeAlternantPoint_injective_of_noAdjacent r k x hx

/--
[sixVertexFixedChargeLimitingWave_ne_zero_of_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityNonzero.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingWave_ne_zero_of_noAdjacent_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  sixVertexFixedChargeLimitingWave r k x ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingWave_ne_zero_of_noAdjacent r k x hx


-- created on 2026-10-23
