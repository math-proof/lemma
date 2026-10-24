import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheGaugeAsymptotics
open Filter Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexFiniteDensityContinuumErrorOfLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean)
-/
@[path]
private lemma tendsto_sixVertexFiniteDensityContinuumErrorOfLower_eq
  {c : Real}
  {lower : Real}
-- given
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun N : Nat => sixVertexFiniteDensityContinuumErrorOfLower c N lower) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFiniteDensityContinuumErrorOfLower c hlower

/--
[tendsto_sixVertexSymmetricJacobianDiagonalErrorOfLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean)
-/
@[path]
private lemma tendsto_sixVertexSymmetricJacobianDiagonalErrorOfLower_eq
  {c : Real}
  {lower : Real}
-- given
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun N : Nat => sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSymmetricJacobianDiagonalErrorOfLower c hlower

/--
[tendsto_sixVertexSymmetricJacobianOffDiagonalErrorOfLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean)
-/
@[path]
private lemma tendsto_sixVertexSymmetricJacobianOffDiagonalErrorOfLower_eq
  {c : Real}
  {lower : Real}
-- given
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun N : Nat => sixVertexSymmetricJacobianOffDiagonalErrorOfLower c N lower) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSymmetricJacobianOffDiagonalErrorOfLower c hlower

/--
[tendsto_sixVertexSymmetricJacobianTotalErrorOfLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean)
-/
@[path]
private lemma tendsto_sixVertexSymmetricJacobianTotalErrorOfLower_eq
  {c : Real}
  {lower : Real}
-- given
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun N : Nat => sixVertexSymmetricJacobianTotalErrorOfLower c N lower) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSymmetricJacobianTotalErrorOfLower c hlower

/--
[sixVertexDensityGaugeOuterRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean)
-/
@[path]
private lemma sixVertexDensityGaugeOuterRadius_pos_eq
  {c rhoLower : Real}
-- given
  (hc : 2 < c)
  (hrho : 0 < rhoLower) :
-- imply
  0 < sixVertexDensityGaugeOuterRadius c rhoLower := by
-- proof
  apply StatMech.FrontierD.sixVertexDensityGaugeOuterRadius_pos hc hrho

/--
[sixVertexDensityGaugeInner_lt_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean)
-/
@[path]
private lemma sixVertexDensityGaugeInner_lt_outer_eq
  {c rhoLower : Real}
-- given
  (hc : 2 < c)
  (hrho : 0 < rhoLower) :
-- imply
  sixVertexDensityGaugeInnerRadius c rhoLower < sixVertexDensityGaugeOuterRadius c rhoLower := by
-- proof
  apply StatMech.FrontierD.sixVertexDensityGaugeInner_lt_outer hc hrho

/--
[sixVertexDensityGaugeOuterRadius_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean)
-/
@[path]
private lemma sixVertexDensityGaugeOuterRadius_le_half_eq
  {c rhoLower : Real}
-- given
  (hc : 2 < c)
  (hrho : 0 ≤ rhoLower) :
-- imply
  sixVertexDensityGaugeOuterRadius c rhoLower ≤ rhoLower * ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) / 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDensityGaugeOuterRadius_le_half hc hrho

/--
[eventually_sixVertexDensityGaugeNumericalMargins](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean)
-/
@[path]
private lemma eventually_sixVertexDensityGaugeNumericalMargins_eq
  {c rhoLower : Real}
-- given
  (hc : 2 < c)
  (hrho : 0 < rhoLower) :
-- imply
  ∀ᶠ N : Nat in atTop, sixVertexRootDensityContractionRate c * sixVertexDensityGaugeOuterRadius c rhoLower + sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) ≤ sixVertexDensityGaugeInnerRadius c rhoLower ∧ sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) < 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexDensityGaugeNumericalMargins hc hrho


-- created on 2026-10-23
