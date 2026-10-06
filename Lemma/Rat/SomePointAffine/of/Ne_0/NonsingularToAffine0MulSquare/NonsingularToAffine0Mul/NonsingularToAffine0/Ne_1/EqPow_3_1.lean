import Mathlib
import sympy.Basic

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

/--
[WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one.lean)
-/

private lemma  ws13_some_congr {k : Type*} [Field k] {V : Affine k} {x₁ x₂ y₁ y₂ : k}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl
@[main]
private lemma main
  [Field k] [DecidableEq k]
  {B w : k}
  {x y : k}
-- given
  (hw : w ^ 3 = 1)
  (hw1 : w ≠ 1)
  (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular x y)
  (hwx : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w * x) y)
  (hw2x : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w ^ 2 * x) y)
  (hx : x ≠ 0) :
-- imply
  (WeierstrassCurve.Affine.Point.some x y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some (w * x) y hwx
      = -(WeierstrassCurve.Affine.Point.some (w ^ 2 * x) y hw2x) := by
-- proof
  have hsum : 1 + w + w ^ 2 = 0 := by
    have h0 : (w - 1) * (1 + w + w ^ 2) = 0 := by linear_combination hw
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hw1
    · exact h1
  have hxne : x ≠ w * x := by
    intro heq
    have h0 : (1 - w) * x = 0 := by linear_combination heq
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hw1 (by linear_combination -h1)
    · exact hx h1
  rw [Point.add_of_X_ne hxne, Point.neg_some]
  refine ws13_some_congr ?_ ?_
  · rw [slope_of_X_ne hxne, sub_self, zero_div]
    simp only [Affine.addX]
    linear_combination -x * hsum
  · rw [slope_of_X_ne hxne, sub_self, zero_div]
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
    ring


-- created on 2026-10-05
