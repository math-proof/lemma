import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetBoundary
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalEvenOffsetBoundarySource_eq_boundarySums](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetBoundary.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenOffsetBoundarySource_eq_boundarySums_eq
  {c : Real}
  {s k : Nat}
  {j : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalEvenOffsetBoundarySource hc s k j = (∑ i : Fin s, sixVertexTheta c (sixVertexCanonicalEvenAlignedHalfRoots hc s k j) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k) (sixVertexCanonicalEvenLeftBoundaryIndex s k i))) + ∑ i : Fin s, sixVertexTheta c (sixVertexCanonicalEvenAlignedHalfRoots hc s k j) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k) (sixVertexCanonicalEvenRightBoundaryIndex s k i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenOffsetBoundarySource_eq_boundarySums hc s k j

/--
[abs_sixVertexCanonicalEvenOffsetBoundarySource_sub_continuous_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetBoundary.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalEvenOffsetBoundarySource_sub_continuous_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + k)) ((2 * s + k + 1) + (2 * s + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)) y) :
-- imply
  |sixVertexCanonicalEvenOffsetBoundarySource hc s k j - (2 * s : Real) * sixVertexContinuousOffsetSource c (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)| <= 2 * (s : Real) ^ 2 * (sixVertexThetaRightLipschitzNNReal c : Real) / ((sixVertexFourWidth 0 (2 * s + k) : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalEvenOffsetBoundarySource_sub_continuous_le hc s k hlower hdensity j

/--
[sixVertexCanonicalOddOffsetBoundarySource_eq_boundary_add_midpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetBoundary.lean)
-/
@[path]
private lemma sixVertexCanonicalOddOffsetBoundarySource_eq_boundary_add_midpoint_eq
  {c : Real}
  {s k : Nat}
  {j : Fin ((((s + k + 1) + 1) + (s + k + 1)))}
-- given
  (hc : 2 < c) :
-- imply
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) let xL := p (sixVertexCanonicalOddLowerHalfIndex s k j) let xU := p (sixVertexCanonicalOddUpperHalfIndex s k j) let x := (xL + xU) / 2 sixVertexCanonicalOddOffsetBoundarySource hc s k j = ((∑ i : Fin s, sixVertexTheta c xL (p ⟨i, by omega⟩)) + (∑ i : Fin (s + 1), sixVertexTheta c xL (p ⟨s + (((s + k + 1) + 1) + (s + k + 1)) + i, by omega⟩)) + (∑ i : Fin (s + 1), sixVertexTheta c xU (p ⟨i, by omega⟩)) + (∑ i : Fin s, sixVertexTheta c xU (p ⟨s + 1 + (((s + k + 1) + 1) + (s + k + 1)) + i, by omega⟩))) / 2 + ((∑ l : Fin ((((s + k + 1) + 1) + (s + k + 1))), sixVertexTheta c xL (p ⟨s + l, by have hl := l.isLt omega⟩)) + (∑ l : Fin ((((s + k + 1) + 1) + (s + k + 1))), sixVertexTheta c xU (p ⟨s + 1 + l, by have hl := l.isLt omega⟩))) / 2 - ∑ l : Fin ((((s + k + 1) + 1) + (s + k + 1))), sixVertexTheta c x (sixVertexCanonicalOddAlignedHalfRoots hc s k l) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddOffsetBoundarySource_eq_boundary_add_midpoint hc s k j

/--
[sixVertexCanonicalOddAlignedHalfGap_le_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetBoundary.lean)
-/
@[path]
private lemma sixVertexCanonicalOddAlignedHalfGap_le_of_finiteDensityLower_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin ((((s + k + 1) + 1) + (s + k + 1)))}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k)) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) y) :
-- imply
  sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) (sixVertexCanonicalOddUpperHalfIndex s k j) - sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) (sixVertexCanonicalOddLowerHalfIndex s k j) <= 1 / ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddAlignedHalfGap_le_of_finiteDensityLower hc s k hlower hdensity j

/--
[abs_sixVertexCanonicalOddOffsetBoundarySource_sub_continuous_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetBoundary.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalOddOffsetBoundarySource_sub_continuous_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin ((((s + k + 1) + 1) + (s + k + 1)))}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k)) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) y) :
-- imply
  |sixVertexCanonicalOddOffsetBoundarySource hc s k j - (2 * s + 1 : Real) * sixVertexContinuousOffsetSource c (sixVertexCanonicalOddAlignedHalfRoots hc s k j)| <= (2 * s + 1 : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) / ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) + ((((s + k + 1) + 1) + (s + k + 1)) : Real) * sixVertexThetaTaylorBound c / (((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) ^ 2) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalOddOffsetBoundarySource_sub_continuous_le hc s k hlower hdensity j


-- created on 2026-10-23
