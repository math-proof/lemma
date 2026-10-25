import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenOffsetNodalNonperiodic
open StatMech StatMech.FrontierD


/--
[abs_evenChargeDensityOffset_sub_continuous_le_tail_of_quadrature](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalNonperiodic.lean)
-/
@[path]
private lemma abs_evenChargeDensityOffset_sub_continuous_le_tail_of_quadrature_eq
  {c : Real}
  {s k : Nat}
  {tau : Real -> Real}
  {testError : Real}
  {i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (htauOdd : Function.Odd tau)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hquad : forall i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k), |(∑ l, sixVertexContinuousOffsetKernel c (sixVertexFixedChargeBetheRoots hc (2 * s) k i) (sixVertexFixedChargeBetheRoots hc (2 * s) k l) * tau (sixVertexFixedChargeBetheRoots hc (2 * s) k l) / sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k l)) / sixVertexFourWidth (2 * s) k - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c (sixVertexFixedChargeBetheRoots hc (2 * s) k i) y * tau y| <= testError)
  (hmargin : 0 < sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth (2 * s) k) (2 * s)) :
-- imply
  |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k i) * sixVertexEvenChargeBetheOffset hc s k i - (2 * s : Real) * tau (sixVertexFixedChargeBetheRoots hc (2 * s) k i)| <= sixVertexEvenOffsetNodalErrorOfTest c s (sixVertexFourWidth (2 * s) k) testError / sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth (2 * s) k) (2 * s) := by
-- proof
  apply StatMech.FrontierD.abs_evenChargeDensityOffset_sub_continuous_le_tail_of_quadrature hc htail s k htauOdd htauEq hquad hmargin i

/--
[tendsto_sixVertexEvenOffsetNodalError_nonperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalNonperiodic.lean)
-/
@[path]
private lemma tendsto_sixVertexEvenOffsetNodalError_nonperiodic_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexEvenOffsetNodalErrorOfTest c s (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeNonperiodicOffsetTestError c (sixVertexFourWidth (2 * s) k) (2 * s) (sixVertexTailFiniteDensityFloor c) G D)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexEvenOffsetNodalError_nonperiodic hc htail s G D

/--
[eventually_uniform_evenChargeDensityOffset_nonperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalNonperiodic.lean)
-/
@[path]
private lemma eventually_uniform_evenChargeDensityOffset_nonperiodic_eq
  {c : Real}
  {s : Nat}
  {tau : Real -> Real}
  {D : NNReal}
  {G : Real}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (htauLip : LipschitzWith D tau)
  (htauBound : forall y, |tau y| <= G)
  (htauOdd : Function.Odd tau)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, ∀ i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k), |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k i) * sixVertexEvenChargeBetheOffset hc s k i - (2 * s : Real) * tau (sixVertexFixedChargeBetheRoots hc (2 * s) k i)| < epsilon := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_evenChargeDensityOffset_nonperiodic hc htail s htauLip htauBound htauOdd htauEq hepsilon


-- created on 2026-10-23
