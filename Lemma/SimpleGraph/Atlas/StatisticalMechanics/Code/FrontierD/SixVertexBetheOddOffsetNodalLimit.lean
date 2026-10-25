import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
open StatMech StatMech.FrontierD


/--
[lipschitzWith_sixVertexContinuousOffsetSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalLimit.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexContinuousOffsetSource_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  LipschitzWith (sixVertexThetaRightLipschitzNNReal c) (sixVertexContinuousOffsetSource c) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexContinuousOffsetSource hc

/--
[abs_oddChargeDensityOffset_sub_continuous_le_tail_of_quadrature](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalLimit.lean)
-/
@[path]
private lemma abs_oddChargeDensityOffset_sub_continuous_le_tail_of_quadrature_eq
  {c : Real}
  {s k : Nat}
  {tau : Real -> Real}
  {testError : Real}
  {i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (htauOdd : Function.Odd tau)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hquad : forall i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k), |(∑ l, sixVertexContinuousOffsetKernel c (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l) * tau (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l) / sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)) / sixVertexFourWidth (2 * s + 1) k - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i) y * tau y| <= testError)
  (hmargin : 0 < sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)) :
-- imply
  |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i) * sixVertexOddChargeBetheOffset hc s k i - (2 * s + 1 : Real) * tau (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i)| <= sixVertexOddOffsetNodalError c s (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) testError / sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) := by
-- proof
  apply StatMech.FrontierD.abs_oddChargeDensityOffset_sub_continuous_le_tail_of_quadrature hc htail s k htauOdd htauEq hquad hmargin i


-- created on 2026-10-23
