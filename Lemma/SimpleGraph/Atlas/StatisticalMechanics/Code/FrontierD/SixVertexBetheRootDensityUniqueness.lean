import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityUniqueness
open StatMech StatMech.FrontierD


/--
[one_div_sixVertexRootDensityWeight_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityUniqueness.lean)
-/
@[path]
private lemma one_div_sixVertexRootDensityWeight_upper_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  1 / sixVertexRootDensityWeight c x <= sixVertexRootDensityScale c / (sixVertexAnisotropyMagnitude c - 1) := by
-- proof
  apply StatMech.FrontierD.one_div_sixVertexRootDensityWeight_upper hc x

/--
[abs_selectedDensityIntegral_sub_tailDensityIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityUniqueness.lean)
-/
@[path]
private lemma abs_selectedDensityIntegral_sub_tailDensityIntegral_le_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  |(∫ y in -Real.pi..Real.pi, sixVertexSelectedFiniteRootDensity hc k y) - ∫ y in -Real.pi..Real.pi, sixVertexTailRootDensity hc htail y| <= 2 * Real.pi * (sixVertexRootDensityScale c / (sixVertexAnisotropyMagnitude c - 1)) * dist (sixVertexSelectedWeightedDensityMap hc k) (sixVertexTailWeightedDensityLimitMap hc htail) := by
-- proof
  apply StatMech.FrontierD.abs_selectedDensityIntegral_sub_tailDensityIntegral_le hc htail k

/--
[intervalIntegral_sixVertexTailRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityUniqueness.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexTailRootDensity_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∫ y in -Real.pi..Real.pi, sixVertexTailRootDensity hc htail y = 1 / 2 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexTailRootDensity hc htail

/--
[sixVertexRootDensity_continuumEquation_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityUniqueness.lean)
-/
@[path]
private lemma sixVertexRootDensity_continuumEquation_unique_eq
  {c : Real}
  {rho sigma : Real → Real}
-- given
  (hc : 2 < c)
  (hrho : Continuous rho)
  (hsigma : Continuous sigma)
  (hrhoMass : (∫ y in -Real.pi..Real.pi, rho y) = 1 / 2)
  (hsigmaMass : (∫ y in -Real.pi..Real.pi, sigma y) = 1 / 2)
  (hrhoEq : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, sixVertexRootDensityWeight c x * rho x = sixVertexRootDensityWeight c x / (2 * Real.pi) - (1 / (2 * Real.pi)) * ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * rho y)
  (hsigmaEq : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, sixVertexRootDensityWeight c x * sigma x = sixVertexRootDensityWeight c x / (2 * Real.pi) - (1 / (2 * Real.pi)) * ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sigma y) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, rho x = sigma x := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensity_continuumEquation_unique hc hrho hsigma hrhoMass hsigmaMass hrhoEq hsigmaEq


-- created on 2026-10-23
