import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFiniteResidual.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexEvenChargeBetheOffset_eq_boundary_add_commonDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean)
-/
@[path]
private lemma sixVertexEvenChargeBetheOffset_eq_boundary_add_commonDifference_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenChargeBetheOffset hc s k j = sixVertexEvenChargeOffsetBoundarySource hc s k j + ∑ l, (sixVertexTheta c (sixVertexEvenChargeAlignedHalfRoots hc s k j) (sixVertexEvenChargeAlignedHalfRoots hc s k l) - sixVertexTheta c (sixVertexFixedChargeBetheRoots hc (2 * s) k j) (sixVertexFixedChargeBetheRoots hc (2 * s) k l)) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeBetheOffset_eq_boundary_add_commonDifference hc s k j

/--
[abs_sixVertexEvenChargeOffsetNodalResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean)
-/
@[path]
private lemma abs_sixVertexEvenChargeOffsetNodalResidual_le_eq
  {c : Real}
  {s k : Nat}
  {B : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c)
  (hB : 0 ≤ B)
  (hoffset : ∀ j, |sixVertexEvenChargeBetheOffset hc s k j| ≤ B) :
-- imply
  |sixVertexEvenChargeOffsetNodalResidual hc s k j| ≤ 4 * sixVertexThetaTaylorBound c * B ^ 2 / sixVertexFourWidth (2 * s) k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexEvenChargeOffsetNodalResidual_le hc s k hB hoffset j

/--
[sixVertexOddChargeBetheOffset_eq_boundary_add_commonDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean)
-/
@[path]
private lemma sixVertexOddChargeBetheOffset_eq_boundary_add_commonDifference_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexOddChargeBetheOffset hc s k j = sixVertexOddChargeOffsetBoundarySource hc s k j + ∑ l, (sixVertexTheta c (sixVertexOddChargeAlignedHalfRoots hc s k j) (sixVertexOddChargeAlignedHalfRoots hc s k l) - sixVertexTheta c (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeBetheOffset_eq_boundary_add_commonDifference hc s k j

/--
[abs_sixVertexOddChargeOffsetNodalResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean)
-/
@[path]
private lemma abs_sixVertexOddChargeOffsetNodalResidual_le_eq
  {c : Real}
  {s k : Nat}
  {B : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c)
  (hB : 0 ≤ B)
  (hoffset : ∀ j, |sixVertexOddChargeBetheOffset hc s k j| ≤ B) :
-- imply
  |sixVertexOddChargeOffsetNodalResidual hc s k j| ≤ 4 * sixVertexThetaTaylorBound c * B ^ 2 / sixVertexFourWidth (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOddChargeOffsetNodalResidual_le hc s k hB hoffset j

/--
[abs_sixVertexEvenChargeOffsetNodalResidual_le_of_densityClose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean)
-/
@[path]
private lemma abs_sixVertexEvenChargeOffsetNodalResidual_le_of_densityClose_eq
  {c : Real}
  {s k : Nat}
  {rho : Real → Real}
  {EP EQ lower : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c)
  (hEP : 0 ≤ EP)
  (hEQ : 0 ≤ EQ)
  (hlower : 0 < lower)
  (hfixedLower : ∀ x, lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) x)
  (hhalfClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((2 * s + k + 1) + (2 * s + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + k)) y - rho y)| ≤ EP / sixVertexFourWidth (2 * s) k)
  (hfixedClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) y - rho y)| ≤ EQ / sixVertexFourWidth (2 * s) k) :
-- imply
  |sixVertexEvenChargeOffsetNodalResidual hc s k j| ≤ 4 * sixVertexThetaTaylorBound c * ((((EP + EQ) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / lower) * Real.pi) ^ 2 / sixVertexFourWidth (2 * s) k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexEvenChargeOffsetNodalResidual_le_of_densityClose hc s k hEP hEQ hlower hfixedLower hhalfClose hfixedClose j

/--
[abs_sixVertexOddChargeOffsetNodalResidual_le_of_densityClose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean)
-/
@[path]
private lemma abs_sixVertexOddChargeOffsetNodalResidual_le_of_densityClose_eq
  {c : Real}
  {s k : Nat}
  {rho : Real → Real}
  {EP EQ lowerP lowerQ : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c)
  (hEP : 0 ≤ EP)
  (hEQ : 0 ≤ EQ)
  (hlowerP : 0 < lowerP)
  (hlowerQ : 0 < lowerQ)
  (hhalfLower : ∀ x, lowerP ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) x)
  (hfixedLower : ∀ x, lowerQ ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) x)
  (hhalfClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) y - rho y)| ≤ EP / sixVertexFourWidth (2 * s + 1) k)
  (hfixedClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) y - rho y)| ≤ EQ / sixVertexFourWidth (2 * s + 1) k) :
-- imply
  |sixVertexOddChargeOffsetNodalResidual hc s k j| ≤ 4 * sixVertexThetaTaylorBound c * (((((EP + EQ) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / lowerQ) * Real.pi + (sixVertexFiniteRootDensityLipschitzConstant c : Real) / (4 * lowerP ^ 2 * lowerQ)) ^ 2) / sixVertexFourWidth (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOddChargeOffsetNodalResidual_le_of_densityClose hc s k hEP hEQ hlowerP hlowerQ hhalfLower hfixedLower hhalfClose hfixedClose j


-- created on 2026-10-23
