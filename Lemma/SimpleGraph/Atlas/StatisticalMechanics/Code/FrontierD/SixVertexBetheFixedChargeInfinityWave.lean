import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityWave.Part5
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexFixedChargeLimitingMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeLimitingMonomial_eq
  {r k : Nat}
  {sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  Tendsto (fun c => sixVertexBetheMonomial (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma x) atTop (nhds (sixVertexFixedChargeLimitingMonomial r k sigma x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeLimitingMonomial r k sigma x

/--
[tendsto_sixVertexFixedChargeNormalizedWave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeNormalizedWave_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  Tendsto (fun c => sixVertexFixedChargeNormalizedWave r k c x) atTop (nhds (sixVertexFixedChargeLimitingWave r k x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeNormalizedWave r k x

/--
[sixVertexFixedChargeLimitingWave_eq_alternant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingWave_eq_alternant_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  sixVertexFixedChargeLimitingWave r k x = ∑ sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k)), (((Equiv.Perm.sign sigma : Int) : Complex)) * ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^ sixVertexFixedChargeAlternantExponent r k x i := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingWave_eq_alternant r k x

/--
[sixVertexFixedChargeLimitingWave_eq_det_alternant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingWave_eq_det_alternant_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  sixVertexFixedChargeLimitingWave r k x = (sixVertexFixedChargeAlternantMatrix r k x).det := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingWave_eq_det_alternant r k x

/--
[sixVertexFixedChargeLimitingPhase_eq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingPhase_eq_geometric_eq
  {r k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  sixVertexFixedChargeLimitingPhase r k j = sixVertexFixedChargeLimitingPhaseCenter r k * sixVertexFixedChargeLimitingPhaseStep r k ^ j.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingPhase_eq_geometric r k j

/--
[sixVertexFixedChargeLimitingWave_eq_center_mul_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingWave_eq_center_mul_vandermonde_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  sixVertexFixedChargeLimitingWave r k x = (∏ i, sixVertexFixedChargeLimitingPhaseCenter r k ^ sixVertexFixedChargeAlternantExponent r k x i) * (Matrix.vandermonde (sixVertexFixedChargeAlternantPoint r k x)).det := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingWave_eq_center_mul_vandermonde r k x


-- created on 2026-10-23
