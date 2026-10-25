import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeBetheContinuationPoint_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheContinuationPoint_parameter_eq
  {a b c : Real}
  {r k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  (sixVertexFixedChargeBetheContinuationPoint ha hc r k).1.1 = c := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheContinuationPoint_parameter ha hc r k

/--
[sixVertexFixedChargeBetheContinuationPoint_roots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheContinuationPoint_roots_eq
  {a b c : Real}
  {r k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  (sixVertexFixedChargeBetheContinuationPoint ha hc r k).1.2 = sixVertexFixedChargeBetheRoots (ha.trans_le hc.1) r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheContinuationPoint_roots ha hc r k

/--
[sixVertexFixedChargeBetheContinuationPoint_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheContinuationPoint_projection_eq
  {a b c : Real}
  {r k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  sixVertexBetheContinuationProjection (sixVertexFixedChargeBetheContinuationPoint ha hc r k) = ⟨c, hc⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheContinuationPoint_projection ha hc r k

/--
[sixVertexFixedChargeContinuationGauge_le_anisotropyError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma sixVertexFixedChargeContinuationGauge_le_anisotropyError_eq
  {a b c : Real}
  {r k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexFixedChargeBetheContinuationPoint ha hc r k) ≤ ((1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) + (r : Real) / sixVertexFourWidth r k) / (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeContinuationGauge_le_anisotropyError ha hc r k

/--
[sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count_eq
  {c : Real}
  {N q r : Nat}
  {p : Fin q → Real}
  {rho : C(Real, Real)}
  {lower E : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hq : 0 < q)
  (hcharge : N = 2 * q + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N q p)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N q p x)
  (hE : 0 ≤ E)
  (hgauge : sixVertexWeightedFiniteDensityGauge hc N q p rho ≤ E) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc N q p rho ≤ sixVertexRootDensityContractionRate c * E + sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count hc hN hq hcharge hopen hsol rho hrhoEq hrhoMass hlower hdensity hE hgauge

/--
[sixVertexFixedChargeWeightedFiniteDensityGauge_le_invWidth_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma sixVertexFixedChargeWeightedFiniteDensityGauge_le_invWidth_tail_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFourierPhysicalDensityMap hc) ≤ (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r (sixVertexTailFiniteDensityFloor c) / (1 - sixVertexRootDensityContractionRate c)) / sixVertexFourWidth r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeWeightedFiniteDensityGauge_le_invWidth_tail hc htail r k

/--
[sixVertexHalfFilledWeightedFiniteDensityGauge_le_invWidth_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma sixVertexHalfFilledWeightedFiniteDensityGauge_le_invWidth_tail_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) (sixVertexFourierPhysicalDensityMap hc) ≤ (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 0 (sixVertexTailFiniteDensityFloor c) / (1 - sixVertexRootDensityContractionRate c)) / sixVertexFourWidth 0 k := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledWeightedFiniteDensityGauge_le_invWidth_tail hc htail k

/--
[tendsto_sixVertexFixedChargeWeightedFiniteDensityGauge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeWeightedFiniteDensityGauge_tail_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k : Nat => sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFourierPhysicalDensityMap hc)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeWeightedFiniteDensityGauge_tail hc htail r

/--
[tendsto_sixVertexFixedChargeContinuationGauge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeContinuationGauge_tail_eq
  {a b c : Real}
  {r : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k : Nat => sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexFixedChargeBetheContinuationPoint ha hc r k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeContinuationGauge_tail ha hc htail r

/--
[eventually_sixVertexFixedChargeContinuationGauge_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean)
-/
@[path]
private lemma eventually_sixVertexFixedChargeContinuationGauge_lt_eq
  {a outer : Real}
  {r k : Nat}
-- given
  (ha : 2 < a)
  (hcharge : (r : Real) / sixVertexFourWidth r k < outer * (2 * Real.pi)) :
-- imply
  ∀ᶠ c : Real in atTop, ∀ b (hc : c ∈ Set.Icc a b), sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexFixedChargeBetheContinuationPoint ha hc r k) < outer := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedChargeContinuationGauge_lt ha r k hcharge


-- created on 2026-10-23
