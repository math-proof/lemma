import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexRootDensityScale_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma sixVertexRootDensityScale_bounds_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexAnisotropyMagnitude c - 1 ≤ sixVertexRootDensityScale c ∧ sixVertexRootDensityScale c ≤ sixVertexAnisotropyMagnitude c := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityScale_bounds hc

/--
[abs_sixVertexRootDensityKernel_sub_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma abs_sixVertexRootDensityKernel_sub_one_le_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexRootDensityKernel c x y - 1| ≤ 1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexRootDensityKernel_sub_one_le hc x y

/--
[sixVertexWeightedFiniteDensityGauge_le_anisotropyError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_le_anisotropyError_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {rho : C(Real, Real)}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : (n : Real) / N = 1 / 2)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
  (hrhoNonneg : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, 0 ≤ rho y) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc N n p rho ≤ (1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) / (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_le_anisotropyError hc hN hhalf p rho hrhoEq hrhoMass hrhoNonneg

/--
[sixVertexHalfFilledContinuationGauge_le_anisotropyError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma sixVertexHalfFilledContinuationGauge_le_anisotropyError_eq
  {a b c : Real}
  {k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexHalfFilledBetheContinuationPoint ha hc k) ≤ (1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) / (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledContinuationGauge_le_anisotropyError ha hc k

/--
[sixVertexFourierRootDensity_ge_quarter_of_nine_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma sixVertexFourierRootDensity_ge_quarter_of_nine_le_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c)
  (hd9 : 9 ≤ sixVertexAnisotropyMagnitude c) :
-- imply
  1 / 4 ≤ sixVertexFourierRootDensity (sixVertexAntiferroelectricLambda c) alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierRootDensity_ge_quarter_of_nine_le hc hd9 alpha

/--
[sixVertexFourierPhysicalDensity_ge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensity_ge_tail_eq
  {c : Real}
  {x : Real}
-- given
  (hc5 : 5 ≤ c) :
-- imply
  1 / (16 * Real.pi) ≤ sixVertexFourierPhysicalDensity c (by linarith) x := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensity_ge_tail hc5 x

/--
[exists_uniformLower_sixVertexFourierPhysicalDensity_Ici](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma exists_uniformLower_sixVertexFourierPhysicalDensity_Ici_eq
  {a : Real}
-- given
  (ha : 2 < a) :
-- imply
  ∃ rhoLower : Real, 0 < rhoLower ∧ ∀ (c) (hac : a ≤ c) (x), rhoLower ≤ sixVertexFourierPhysicalDensity c (ha.trans_le hac) x := by
-- proof
  apply StatMech.FrontierD.exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha

/--
[tendsto_sixVertexAnisotropyGaugeError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma tendsto_sixVertexAnisotropyGaugeError_eq :
-- imply
  Tendsto (fun c : Real => (1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) / (2 * Real.pi)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexAnisotropyGaugeError

/--
[exists_uniform_sixVertexCoefficientBounds_Ici](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma exists_uniform_sixVertexCoefficientBounds_Ici_eq
  {a : Real}
-- given
  (ha : 2 < a) :
-- imply
  ∃ kernelB thetaB ratioB boundaryB : Real, 0 < kernelB ∧ 0 < thetaB ∧ 0 < ratioB ∧ boundaryB < 2 * Real.pi ∧ ∀ c, a ≤ c → sixVertexRootDensityKernelLipschitzBound c ≤ kernelB ∧ sixVertexThetaLeftKernelLipschitzBound c ≤ thetaB ∧ sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1) ≤ ratioB ∧ sixVertexSymmetricScatteringBoundaryBound c ≤ boundaryB := by
-- proof
  apply StatMech.FrontierD.exists_uniform_sixVertexCoefficientBounds_Ici ha

/--
[sixVertexRootDensityWeightFloor_ge_inv_of_ratio_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma sixVertexRootDensityWeightFloor_ge_inv_of_ratio_le_eq
  {c R : Real}
-- given
  (hc : 2 < c)
  (hR : 0 < R)
  (hratio : sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1) ≤ R) :
-- imply
  1 / R ≤ (sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeightFloor_ge_inv_of_ratio_le hc hR hratio

/--
[sixVertexRootDensityContractionRate_le_of_ratio_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma sixVertexRootDensityContractionRate_le_of_ratio_le_eq
  {c R : Real}
-- given
  (hc : 2 < c)
  (hR : 0 < R)
  (hratio : sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1) ≤ R) :
-- imply
  sixVertexRootDensityContractionRate c ≤ 1 - 1 / (10 * R ^ 3) := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityContractionRate_le_of_ratio_le hc hR hratio

/--
[exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici_eq
  {a rhoLower : Real}
-- given
  (ha : 2 < a)
  (hrhoLower : 0 < rhoLower) :
-- imply
  ∃ inner outer : Real, 0 < outer ∧ inner < outer ∧ (∀ c, a ≤ c → outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) / 2) ∧ ∀ᶠ N : Nat in atTop, ∀ c, a ≤ c → sixVertexRootDensityContractionRate c * outer + sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) ≤ inner ∧ sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) < 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici ha hrhoLower

/--
[eventually_sixVertexHalfFilledContinuationGauge_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheInfiniteAnisotropyGauge.lean)
-/
@[path]
private lemma eventually_sixVertexHalfFilledContinuationGauge_lt_eq
  {a outer : Real}
  {k : Nat}
-- given
  (ha : 2 < a)
  (houter : 0 < outer) :
-- imply
  ∀ᶠ c : Real in atTop, ∀ (b) (hc : c ∈ Set.Icc a b), sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexHalfFilledBetheContinuationPoint ha hc k) < outer := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexHalfFilledContinuationGauge_lt ha houter k


-- created on 2026-10-23
