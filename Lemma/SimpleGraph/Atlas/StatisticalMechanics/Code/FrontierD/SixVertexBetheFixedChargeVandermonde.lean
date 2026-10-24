import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexFixedChargeNormalizedBethePairFactorAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeNormalizedBethePairFactorAt_eq
  {r k : Nat}
  {i j : Fin (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  Tendsto (fun c => sixVertexNormalizedBethePairFactor c (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c)) (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c))) atTop (nhds (sixVertexFixedChargeLimitingPhase r k i)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeNormalizedBethePairFactorAt r k i j

/--
[tendsto_sixVertexFixedChargeNormalizedAmplitude](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeNormalizedAmplitude_eq
  {r k : Nat}
  {sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))} :
-- imply
  Tendsto (sixVertexFixedChargeNormalizedAmplitude r k · sigma) atTop (nhds ((((Equiv.Perm.sign sigma : Int) : Complex)) * ∏ i, ∏ _j ∈ Finset.Ioi i, sixVertexFixedChargeLimitingPhase r k (sigma i))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeNormalizedAmplitude r k sigma

/--
[tendsto_sixVertexFixedChargeNormalizedAlternatingWave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeNormalizedAlternatingWave_eq
  {r k : Nat} :
-- imply
  Tendsto (sixVertexFixedChargeNormalizedAlternatingWave r k) atTop (nhds (sixVertexFixedChargeVandermondeSum r k)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeNormalizedAlternatingWave r k

/--
[sixVertexFixedChargeVandermondeSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean)
-/
@[path]
private lemma sixVertexFixedChargeVandermondeSum_eq_eq
  {r k : Nat} :
-- imply
  sixVertexFixedChargeVandermondeSum r k = (∏ i, sixVertexFixedChargeLimitingPhase r k i ^ sixVertexFixedChargeBetheParticleCount r k) * (Matrix.vandermonde (sixVertexFixedChargeLimitingPhase r k)).det := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeVandermondeSum_eq r k

/--
[sixVertexFixedChargeVandermondeSum_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean)
-/
@[path]
private lemma sixVertexFixedChargeVandermondeSum_ne_zero_eq
  {r k : Nat} :
-- imply
  sixVertexFixedChargeVandermondeSum r k ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeVandermondeSum_ne_zero r k

/--
[sixVertexFixedChargePairScaleProduct_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean)
-/
@[path]
private lemma sixVertexFixedChargePairScaleProduct_ne_zero_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexFixedChargePairScaleProduct r k c ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargePairScaleProduct_ne_zero hc r k

/--
[sixVertexFixedChargeCoordinateBetheWave_alternating_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean)
-/
@[path]
private lemma sixVertexFixedChargeCoordinateBetheWave_alternating_eq_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k) (sixVertexAlternatingOddSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheParticleCount_twice_le r k)) = sixVertexFixedChargePairScaleProduct r k c * sixVertexFixedChargeNormalizedAlternatingWave r k c := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeCoordinateBetheWave_alternating_eq hc r k

/--
[eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean)
-/
@[path]
private lemma eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero_eq
  {r k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, ∀ hc : 2 < c, sixVertexCoordinateBetheWave (N := sixVertexFourWidth r k) c (sixVertexFixedChargeBetheRoots hc r k) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero r k


-- created on 2026-10-23
