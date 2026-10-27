import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenOffsetNodalConvergence
open StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeOffsetNetMargin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalConvergence.lean)
-/
@[path]
private lemma sixVertexFixedChargeOffsetNetMargin_eq_eq
  {c : Real}
  {N r : Nat} :
-- imply
  sixVertexFixedChargeOffsetNetMargin c N r = sixVertexFixedChargeOffsetContractionMargin c - sixVertexFixedChargeOffsetRowError c N r (sixVertexTailFiniteDensityFloor c) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeOffsetNetMargin_eq c N r

/--
[tendsto_sixVertexFixedChargeOffsetNetMargin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeOffsetNetMargin_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth r k) r) atTop (nhds (sixVertexFixedChargeOffsetContractionMargin c)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeOffsetNetMargin hc htail r

/--
[eventually_sixVertexFixedChargeOffsetNetMargin_ge_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalConvergence.lean)
-/
@[path]
private lemma eventually_sixVertexFixedChargeOffsetNetMargin_ge_half_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexFixedChargeOffsetContractionMargin c / 2 <= sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth r k) r := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedChargeOffsetNetMargin_ge_half hc htail r

/--
[eventually_sixVertexFixedChargeOffsetNetMargin_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalConvergence.lean)
-/
@[path]
private lemma eventually_sixVertexFixedChargeOffsetNetMargin_pos_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ᶠ k : Nat in atTop, 0 < sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth r k) r := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedChargeOffsetNetMargin_pos hc htail r

/--
[tendsto_sixVertexEvenOffsetNodalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexEvenOffsetNodalError_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexEvenOffsetNodalError c s (sixVertexFourWidth (2 * s) k) G D) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexEvenOffsetNodalError hc htail s G D

/--
[tendsto_sixVertexEvenOffsetNodalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexEvenOffsetNodalBound_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexEvenOffsetNodalError c s (sixVertexFourWidth (2 * s) k) G D / sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth (2 * s) k) (2 * s)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexEvenOffsetNodalBound hc htail s G D

/--
[eventually_uniform_evenChargeDensityOffset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalConvergence.lean)
-/
@[path]
private lemma eventually_uniform_evenChargeDensityOffset_eq
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
  (htauPeriodic : Function.Periodic tau (2 * Real.pi))
  (htauBound : forall y, |tau y| <= G)
  (htauOdd : Function.Odd tau)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, ∀ j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k), := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_evenChargeDensityOffset hc htail s htauLip htauPeriodic htauBound htauOdd htauEq hepsilon


-- created on 2026-10-23
