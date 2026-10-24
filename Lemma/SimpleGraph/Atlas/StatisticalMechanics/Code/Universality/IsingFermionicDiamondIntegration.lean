import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration
open Finset StatMech StatMech.Universality


/--
[isingCenteredSum_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean)
-/
@[path]
private lemma isingCenteredSum_self_eq
  {f : Nat → Real}
  {center : Nat} :
-- imply
  isingCenteredSum f center center = 0 := by
-- proof
  apply StatMech.Universality.isingCenteredSum_self f center

/--
[isingCenteredSum_succ_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean)
-/
@[path]
private lemma isingCenteredSum_succ_sub_eq
  {f : Nat → Real}
  {center i : Nat} :
-- imply
  isingCenteredSum f center (i + 1) - isingCenteredSum f center i = f i := by
-- proof
  apply StatMech.Universality.isingCenteredSum_succ_sub f center i

/--
[isingCenteredPrimitive_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean)
-/
@[path]
private lemma isingCenteredPrimitive_horizontal_increment_eq
  {center i j : Nat}
-- given
  (horizontal vertical : Nat → Nat → Real) :
-- imply
  isingCenteredPrimitive horizontal vertical center (i + 1) j - isingCenteredPrimitive horizontal vertical center i j = horizontal i j := by
-- proof
  apply StatMech.Universality.isingCenteredPrimitive_horizontal_increment horizontal vertical center i j

/--
[isingCenteredSum_row_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean)
-/
@[path]
private lemma isingCenteredSum_row_difference_eq
  {center i j : Nat}
-- given
  (horizontal vertical : Nat → Nat → Real)
  (hclosed : ∀ k, (center ≤ k ∧ k < i) ∨ (i ≤ k ∧ k < center) → vertical k j + horizontal k (j + 1) = horizontal k j + vertical (k + 1) j) :
-- imply
  isingCenteredSum (fun k ↦ horizontal k (j + 1)) center i - isingCenteredSum (fun k ↦ horizontal k j) center i = vertical i j - vertical center j := by
-- proof
  apply StatMech.Universality.isingCenteredSum_row_difference horizontal vertical center i j hclosed

/--
[isingCenteredPrimitive_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean)
-/
@[path]
private lemma isingCenteredPrimitive_vertical_increment_eq
  {center i j : Nat}
-- given
  (horizontal vertical : Nat → Nat → Real)
  (hclosed : ∀ k, (center ≤ k ∧ k < i) ∨ (i ≤ k ∧ k < center) → vertical k j + horizontal k (j + 1) = horizontal k j + vertical (k + 1) j) :
-- imply
  isingCenteredPrimitive horizontal vertical center i (j + 1) - isingCenteredPrimitive horizontal vertical center i j = vertical i j := by
-- proof
  apply StatMech.Universality.isingCenteredPrimitive_vertical_increment horizontal vertical center i j hclosed


-- created on 2026-10-23
