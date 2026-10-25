import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4
open StatMech StatMech.Universality


/--
[taylorWithinEval_three_eq_cubic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean)
-/
@[path]
private lemma taylorWithinEval_three_eq_cubic_eq
  {g : Real → Real}
  {s : Real}
-- given
  (hs : s ≠ 0)
  (hg : ContDiff Real 4 g) :
-- imply
  taylorWithinEval g 3 (uIcc 0 s) 0 s = cubicTaylorPolynomial g s := by
-- proof
  apply StatMech.Universality.taylorWithinEval_three_eq_cubic g s hs hg

/--
[cubicTaylor_remainder_le_of_fourthDeriv_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean)
-/
@[path]
private lemma cubicTaylor_remainder_le_of_fourthDeriv_bound_eq
  {g : Real → Real}
  {s M : Real}
-- given
  (hs : s ≠ 0)
  (hg : ContDiff Real 4 g)
  (hM : ∀ t ∈ uIcc 0 s, |iteratedDeriv 4 g t| ≤ M) :
-- imply
  |g s - cubicTaylorPolynomial g s| ≤ M * |s| ^ 4 / 24 := by
-- proof
  apply StatMech.Universality.cubicTaylor_remainder_le_of_fourthDeriv_bound g s M hs hg hM

/--
[centralSecondDifference_remainder_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean)
-/
@[path]
private lemma centralSecondDifference_remainder_le_eq
  {g : Real → Real}
-- given
  (h M : Real)
  (hg : ContDiff Real 4 g)
  (hfourth : ∀ t, |iteratedDeriv 4 g t| ≤ M) :
-- imply
  |(g h + g (-h) - 2 * g 0) - iteratedDeriv 2 g 0 * h ^ 2| ≤ M * |h| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.centralSecondDifference_remainder_le g h M hg hfourth

/--
[harmonicDirectionalFourNeighborStencil_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean)
-/
@[path]
private lemma harmonicDirectionalFourNeighborStencil_le_eq
  {g₁ g₂ : Real → Real}
-- given
  (h M₁ M₂ : Real)
  (hg₁ : ContDiff Real 4 g₁)
  (hg₂ : ContDiff Real 4 g₂)
  (hfourth₁ : ∀ t, |iteratedDeriv 4 g₁ t| ≤ M₁)
  (hfourth₂ : ∀ t, |iteratedDeriv 4 g₂ t| ≤ M₂)
  (hharmonic : iteratedDeriv 2 g₁ 0 + iteratedDeriv 2 g₂ 0 = 0) :
-- imply
  |directionalFourNeighborStencil g₁ g₂ h| ≤ (M₁ + M₂) * |h| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.harmonicDirectionalFourNeighborStencil_le g₁ g₂ h M₁ M₂ hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

/--
[complexAxialFourNeighborStencil_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean)
-/
@[path]
private lemma complexAxialFourNeighborStencil_le_eq
  {f : Complex → Real}
  {z : Complex}
-- given
  (h M₁ M₂ : Real)
  (hg₁ : ContDiff Real 4 (fun t : Real ↦ f (z + (t : Complex))))
  (hg₂ : ContDiff Real 4 (fun t : Real ↦ f (z + (t : Complex) * Complex.I)))
  (hfourth₁ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f (z + (s : Complex))) t| ≤ M₁)
  (hfourth₂ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f (z + (s : Complex) * Complex.I)) t| ≤ M₂)
  (hharmonic : iteratedDeriv 2 (fun t : Real ↦ f (z + (t : Complex))) 0 + iteratedDeriv 2 (fun t : Real ↦ f (z + (t : Complex) * Complex.I)) 0 = 0) :
-- imply
  |complexAxialFourNeighborStencil f z h| ≤ (M₁ + M₂) * |h| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.complexAxialFourNeighborStencil_le f z h M₁ M₂ hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

/--
[complexDirectionalFourNeighborStencil_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean)
-/
@[path]
private lemma complexDirectionalFourNeighborStencil_le_eq
  {f : Complex → Real}
  {z v₁ v₂ : Complex}
-- given
  (h M₁ M₂ : Real)
  (hg₁ : ContDiff Real 4 (fun t : Real ↦ f (z + (t : Complex) * v₁)))
  (hg₂ : ContDiff Real 4 (fun t : Real ↦ f (z + (t : Complex) * v₂)))
  (hfourth₁ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f (z + (s : Complex) * v₁)) t| ≤ M₁)
  (hfourth₂ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f (z + (s : Complex) * v₂)) t| ≤ M₂)
  (hharmonic : iteratedDeriv 2 (fun t : Real ↦ f (z + (t : Complex) * v₁)) 0 + iteratedDeriv 2 (fun t : Real ↦ f (z + (t : Complex) * v₂)) 0 = 0) :
-- imply
  |complexDirectionalFourNeighborStencil f z v₁ v₂ h| ≤ (M₁ + M₂) * |h| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.complexDirectionalFourNeighborStencil_le f z v₁ v₂ h M₁ M₂ hg₁ hg₂ hfourth₁ hfourth₂ hharmonic


-- created on 2026-10-23
