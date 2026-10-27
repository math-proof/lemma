import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetBoundaryEstimate
open StatMech StatMech.FrontierD


/--
[coe_sixVertexThetaRightLipschitzNNReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma coe_sixVertexThetaRightLipschitzNNReal_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  (sixVertexThetaRightLipschitzNNReal c : Real) = sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1) := by
-- proof
  apply StatMech.FrontierD.coe_sixVertexThetaRightLipschitzNNReal hc

/--
[lipschitzWith_sixVertexTheta_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexTheta_right_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  LipschitzWith (sixVertexThetaRightLipschitzNNReal c) (fun y => sixVertexTheta c x y) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexTheta_right hc x

/--
[sixVertexBetheSolution_sub_first_le_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma sixVertexBetheSolution_sub_first_le_of_finiteDensityLower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) -> Real}
  {lower : Real}
  {i : Fin (n + 1)}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  p i - p 0 <= (i.val : Real) / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_sub_first_le_of_finiteDensityLower hc hN hopen hsol hlower hdensity i

/--
[sixVertexBetheSolution_first_endpoint_le_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma sixVertexBetheSolution_first_endpoint_le_of_finiteDensityLower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) -> Real}
  {lower : Real}
  {i : Fin (n + 1)}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  p i - (-Real.pi) <= ((i.val : Real) + 1) / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_first_endpoint_le_of_finiteDensityLower hc hN hhalf hopen hsol hlower hdensity i

/--
[sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) -> Real}
  {lower : Real}
  {i : Fin (n + 1)}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N (n + 1) p x) :
-- imply
  Real.pi - p i <= ((i.rev.val : Real) + 1) / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower hc hN hhalf hopen hsol hlower hdensity i

/--
[abs_sixVertexEvenChargeOffsetBoundarySource_sub_continuous_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma abs_sixVertexEvenChargeOffsetBoundarySource_sub_continuous_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + k)) ((2 * s + k + 1) + (2 * s + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + k)) y) :
-- imply
  |sixVertexEvenChargeOffsetBoundarySource hc s k j - (2 * s : Real) * sixVertexContinuousOffsetSource c (sixVertexEvenChargeAlignedHalfRoots hc s k j)| <= 2 * (s : Real) ^ 2 * (sixVertexThetaRightLipschitzNNReal c : Real) / ((sixVertexFourWidth 0 (2 * s + k) : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexEvenChargeOffsetBoundarySource_sub_continuous_le hc s k hlower hdensity j


-- created on 2026-10-23
