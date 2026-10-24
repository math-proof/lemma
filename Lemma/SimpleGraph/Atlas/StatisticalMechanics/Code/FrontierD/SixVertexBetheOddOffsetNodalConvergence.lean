import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetNodalConvergence
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexOddOffsetResidualError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexOddOffsetResidualError_eq
  {c : Real}
  {s : Nat} :
-- imply
  Tendsto (fun k => sixVertexOddOffsetResidualError c s (sixVertexFourWidth (2 * s + 1) k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOddOffsetResidualError c s

/--
[tendsto_sixVertexOddOffsetBoundaryError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexOddOffsetBoundaryError_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexOddOffsetBoundaryError c s (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOddOffsetBoundaryError hc htail s

/--
[tendsto_sixVertexOddOffsetSourceMoveError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexOddOffsetSourceMoveError_eq
  {c : Real}
  {s : Nat} :
-- imply
  Tendsto (fun k => sixVertexOddOffsetSourceMoveError c s (sixVertexFourWidth (2 * s + 1) k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOddOffsetSourceMoveError c s

/--
[tendsto_sixVertexOddOffsetNodalError_nonperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexOddOffsetNodalError_nonperiodic_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexOddOffsetNodalError c s (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeNonperiodicOffsetTestError c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) (sixVertexTailFiniteDensityFloor c) G D)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOddOffsetNodalError_nonperiodic hc htail s G D

/--
[tendsto_sixVertexOddOffsetNodalBound_nonperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalConvergence.lean)
-/
@[path]
private lemma tendsto_sixVertexOddOffsetNodalBound_nonperiodic_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexOddOffsetNodalError c s (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeNonperiodicOffsetTestError c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) (sixVertexTailFiniteDensityFloor c) G D) / sixVertexFixedChargeOffsetNetMargin c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOddOffsetNodalBound_nonperiodic hc htail s G D

/--
[eventually_uniform_oddChargeDensityOffset_nonperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalConvergence.lean)
-/
@[path]
private lemma eventually_uniform_oddChargeDensityOffset_nonperiodic_eq
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
  ∀ᶠ k : Nat in atTop, ∀ i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k), := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_oddChargeDensityOffset_nonperiodic hc htail s htauLip htauBound htauOdd htauEq hepsilon


-- created on 2026-10-23
