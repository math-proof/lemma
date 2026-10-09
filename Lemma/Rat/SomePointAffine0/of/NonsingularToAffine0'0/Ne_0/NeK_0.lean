import Mathlib
import sympy.Basic

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

/--
[WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model.lean)
-/

private lemma  ws13_some_congr' {k : Type*} [Field k] {V : Affine k} {x₁ x₂ y₁ y₂ : k}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl
@[path]
private lemma main
  [Field k] [DecidableEq k]
  {B : k}
  {y : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (hy0 : y ≠ 0)
  (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular 0 y) :
-- imply
  (WeierstrassCurve.Affine.Point.some 0 y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some 0 y h
      = -(WeierstrassCurve.Affine.Point.some 0 y h) := by
-- proof
  have hyne : y ≠ Affine.negY (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k) 0 y := by
    simp only [Affine.negY]
    intro heq
    have : (2 : k) * y = 0 := by linear_combination heq
    rcases mul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hy0 h'
  rw [Point.add_of_Y_ne hyne, Point.neg_some]
  refine ws13_some_congr' ?_ ?_
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addX, Affine.negY]
    ring
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
    ring


-- created on 2026-10-05
