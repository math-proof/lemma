import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenOffsetNodalLimit
open Finset StatMech StatMech.FrontierD


/--
[abs_evenChargeDensityOffset_sub_continuous_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalLimit.lean)
-/
@[path]
private lemma abs_evenChargeDensityOffset_sub_continuous_le_tail_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) (htail : 2 < sixVertexAnisotropyMagnitude c) (s k : Nat) {tau : Real -> Real} {D : NNReal} {G : Real} (htauLip : LipschitzWith D tau) (htauPeriodic : Function.Periodic tau (2 * Real.pi)) (htauBound : forall y, |tau y| <= G) (htauOdd : Function.Odd tau) (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau) (hmargin : 0 < sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth (2 * s) k) (2 * s)) (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)), |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k j) * sixVertexEvenChargeBetheOffset hc s k j - (2 * s : Real) * tau (sixVertexFixedChargeBetheRoots hc (2 * s) k j)| <= sixVertexEvenOffsetNodalError c s (sixVertexFourWidth (2 * s) k) G D / sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth (2 * s) k) (2 * s) := by
-- proof
  apply StatMech.FrontierD.abs_evenChargeDensityOffset_sub_continuous_le_tail


-- created on 2026-10-23
