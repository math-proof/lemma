import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetBoundaryEstimate
open StatMech StatMech.FrontierD


/--
[sixVertexOddChargeOffsetBoundarySource_eq_boundary_add_midpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma sixVertexOddChargeOffsetBoundarySource_eq_boundary_add_midpoint_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c) :
-- imply
  let p := sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) let xL := p (sixVertexOddChargeLowerHalfIndex s k j) let xU := p (sixVertexOddChargeUpperHalfIndex s k j) let x := (xL + xU) / 2 sixVertexOddChargeOffsetBoundarySource hc s k j = ((∑ i : Fin s, sixVertexTheta c xL (p ⟨i, by omega⟩)) + (∑ i : Fin (s + 1), sixVertexTheta c xL (p ⟨s + sixVertexFixedChargeBetheParticleCount (2 * s + 1) k + i, by rw [sixVertexFixedChargeBetheParticleCount_eq] omega⟩)) + (∑ i : Fin (s + 1), sixVertexTheta c xU (p ⟨i, by omega⟩)) + (∑ i : Fin s, sixVertexTheta c xU (p ⟨s + 1 + sixVertexFixedChargeBetheParticleCount (2 * s + 1) k + i, by rw [sixVertexFixedChargeBetheParticleCount_eq] omega⟩))) / 2 + ((∑ l : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k), sixVertexTheta c xL (p ⟨s + l, by have hl := l.isLt have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k omega⟩)) + (∑ l : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k), sixVertexTheta c xU (p ⟨s + 1 + l, by have hl := l.isLt have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k omega⟩))) / 2 - ∑ l : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k), sixVertexTheta c x (sixVertexOddChargeAlignedHalfRoots hc s k l) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeOffsetBoundarySource_eq_boundary_add_midpoint hc s k j

/--
[sixVertexOddChargeAlignedHalfGap_le_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma sixVertexOddChargeAlignedHalfGap_le_of_finiteDensityLower_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k)) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) y) :
-- imply
  sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) (sixVertexOddChargeUpperHalfIndex s k j) - sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) (sixVertexOddChargeLowerHalfIndex s k j) <= 1 / ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeAlignedHalfGap_le_of_finiteDensityLower hc s k hlower hdensity j

/--
[abs_sixVertexTheta_average_sub_midpoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma abs_sixVertexTheta_average_sub_midpoint_le_eq
  {c : Real}
  {xL xU yL yU : Real}
-- given
  (hc : 2 < c) :
-- imply
  |(sixVertexTheta c xL yL + sixVertexTheta c xU yU) / 2 - sixVertexTheta c ((xL + xU) / 2) ((yL + yU) / 2)| <= sixVertexThetaTaylorBound c * (|xU - xL| + |yU - yL|) ^ 2 / 4 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexTheta_average_sub_midpoint_le hc xL xU yL yU

/--
[lipschitzWith_sixVertexTheta_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexTheta_left_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c) :
-- imply
  LipschitzWith (sixVertexThetaRightLipschitzNNReal c) (fun x => sixVertexTheta c x y) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexTheta_left hc y

/--
[abs_sixVertexOddChargeOffsetBoundarySource_sub_continuous_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetBoundaryEstimate.lean)
-/
@[path]
private lemma abs_sixVertexOddChargeOffsetBoundarySource_sub_continuous_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k)) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) y) :
-- imply
  |sixVertexOddChargeOffsetBoundarySource hc s k j - (2 * s + 1 : Real) * sixVertexContinuousOffsetSource c (sixVertexOddChargeAlignedHalfRoots hc s k j)| <= (2 * s + 1 : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) / ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) + (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k : Real) * sixVertexThetaTaylorBound c / (((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) ^ 2) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOddChargeOffsetBoundarySource_sub_continuous_le hc s k hlower hdensity j


-- created on 2026-10-23
