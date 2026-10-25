import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheGaugeUniform
open Filter Topology StatMech StatMech.FrontierD


/--
[continuous_sixVertexAnisotropyMagnitude_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma continuous_sixVertexAnisotropyMagnitude_Icc_eq
  {a b : Real} :
-- imply
  Continuous (fun t : Set.Icc a b => sixVertexAnisotropyMagnitude t.1) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexAnisotropyMagnitude_Icc

/--
[continuous_sixVertexRootDensityScale_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma continuous_sixVertexRootDensityScale_Icc_eq
  {a b : Real} :
-- imply
  Continuous (fun t : Set.Icc a b => sixVertexRootDensityScale t.1) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexRootDensityScale_Icc

/--
[continuous_sixVertexRootDensityWeightFloor_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma continuous_sixVertexRootDensityWeightFloor_Icc_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun t : Set.Icc a b => (sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexRootDensityWeightFloor_Icc ha

/--
[continuous_sixVertexRootDensityContractionRate_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma continuous_sixVertexRootDensityContractionRate_Icc_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun t : Set.Icc a b => sixVertexRootDensityContractionRate t.1) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexRootDensityContractionRate_Icc ha

/--
[continuous_sixVertexSymmetricScatteringBoundaryBound_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma continuous_sixVertexSymmetricScatteringBoundaryBound_Icc_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun t : Set.Icc a b => sixVertexSymmetricScatteringBoundaryBound t.1) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexSymmetricScatteringBoundaryBound_Icc ha

/--
[continuous_sixVertexFiniteDensityErrorOne_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma continuous_sixVertexFiniteDensityErrorOne_Icc_eq
  {a b lower : Real}
-- given
  (ha : 2 < a)
  (_hlower : 0 < lower) :
-- imply
  Continuous (fun t : Set.Icc a b => sixVertexFiniteDensityContinuumErrorOfLower t.1 1 lower) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexFiniteDensityErrorOne_Icc ha _hlower

/--
[continuous_sixVertexJacobianTotalErrorOne_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma continuous_sixVertexJacobianTotalErrorOne_Icc_eq
  {a b lower : Real}
-- given
  (ha : 2 < a)
  (_hlower : 0 < lower) :
-- imply
  Continuous (fun t : Set.Icc a b => sixVertexSymmetricJacobianTotalErrorOfLower t.1 1 lower) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexJacobianTotalErrorOne_Icc ha _hlower

/--
[sixVertexFiniteDensityContinuumErrorOfLower_eq_one_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma sixVertexFiniteDensityContinuumErrorOfLower_eq_one_div_eq
  {c lower : Real}
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexFiniteDensityContinuumErrorOfLower c N lower = sixVertexFiniteDensityContinuumErrorOfLower c 1 lower / N := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteDensityContinuumErrorOfLower_eq_one_div c lower hN

/--
[sixVertexSymmetricJacobianTotalErrorOfLower_eq_one_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma sixVertexSymmetricJacobianTotalErrorOfLower_eq_one_div_eq
  {c lower : Real}
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexSymmetricJacobianTotalErrorOfLower c N lower = sixVertexSymmetricJacobianTotalErrorOfLower c 1 lower / N := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricJacobianTotalErrorOfLower_eq_one_div c lower hN

/--
[exists_uniform_sixVertexDensityGaugeNumericalMargins](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma exists_uniform_sixVertexDensityGaugeNumericalMargins_eq
  {a b rhoLower : Real}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hrhoLower : 0 < rhoLower) :
-- imply
  ∃ inner outer : Real, inner < outer ∧ (∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2) ∧ ∀ᶠ N : Nat in atTop, ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFiniteDensityContinuumErrorOfLower t.1 N (rhoLower / 2) ≤ inner ∧ sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 N (rhoLower / 2) < 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.exists_uniform_sixVertexDensityGaugeNumericalMargins ha hab hrhoLower

/--
[tendsto_sixVertexHalfFilledContinuationGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma tendsto_sixVertexHalfFilledContinuationGauge_eq
  {a b c : Real}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexContinuationWeightedFiniteDensityGauge ha (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexFourierPhysicalDensityFamily ha) (sixVertexHalfFilledBetheContinuationPoint ha hc k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexHalfFilledContinuationGauge ha hc htail

/--
[exists_uniform_sixVertexDensityGaugeMargins_fourWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeUniform.lean)
-/
@[path]
private lemma exists_uniform_sixVertexDensityGaugeMargins_fourWidth_eq
  {a b rhoLower : Real}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hrhoLower : 0 < rhoLower) :
-- imply
  ∃ inner outer : Real, inner < outer ∧ (∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2) ∧ ∀ᶠ k : Nat in atTop, ∀ t : Set.Icc a b, sixVertexRootDensityContractionRate t.1 * outer + sixVertexFiniteDensityContinuumErrorOfLower t.1 (sixVertexFourWidth 0 k) (rhoLower / 2) ≤ inner ∧ sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 (sixVertexFourWidth 0 k) (rhoLower / 2) < 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.exists_uniform_sixVertexDensityGaugeMargins_fourWidth ha hab hrhoLower


-- created on 2026-10-23
