import Mathlib
import Lemma.WeierstrassCurve.VeluQuotientMap
import Macro.WeierstrassCurve_VeluPointMap
import Def.WeierstrassCurve_VeluPointMap

open Polynomial
open scoped WeierstrassCurve.VeluPointMap

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

private lemma eval_Ψ₃_eq (x : R) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  rw [Ψ₃]; eval_simp


theorem velu_singleton_equation_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) :
    W.veluYNum x₀ y₀ x y ^ 2 + W.a₁ * W.veluXNum x₀ y₀ x * W.veluYNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.veluYNum x₀ y₀ x y * (x - x₀) ^ 3
      = W.veluXNum x₀ y₀ x ^ 3 + W.a₂ * W.veluXNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluT x₀ y₀) * W.veluXNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluT x₀ y₀ - 7 * W.veluW x₀ y₀) * (x - x₀) ^ 6 := by
  rw [Affine.equation_iff] at hP hQ
  rw [W.eval_Ψ₃_eq] at hΨ
  simp only [b₂, b₄, b₆, b₈] at hΨ
  simp only [veluXNum, veluYNum, veluT, veluU, veluW, veluGx, veluGy, b₂]
  linear_combination
    (W.a₁^4*x^2*x₀^2 + 2*W.a₁^4*x*x₀^3 + W.a₁^4*x₀^4 + 2*W.a₁^3*W.a₃*x^2*x₀ + 8*W.a₁^3*W.a₃*x*x₀^2 + 6*W.a₁^3*W.a₃*x₀^3 + 16*W.a₁^3*x*x₀^2*y₀ + 16*W.a₁^3*x₀^3*y₀ + 8*W.a₁^2*W.a₂*x^2*x₀^2 - 8*W.a₁^2*W.a₂*x₀^4 + W.a₁^2*W.a₃^2*x^2 + 10*W.a₁^2*W.a₃^2*x*x₀ + 13*W.a₁^2*W.a₃^2*x₀^2 + 32*W.a₁^2*W.a₃*x*x₀*y₀ + 64*W.a₁^2*W.a₃*x₀^2*y₀ + 4*W.a₁^2*W.a₄*x^2*x₀ - 4*W.a₁^2*W.a₄*x₀^3 - 2*W.a₁^2*x^4*x₀ + 4*W.a₁^2*x^3*x₀^2 + 12*W.a₁^2*x^2*x₀^3 - 4*W.a₁^2*x*x₀^4 + 16*W.a₁^2*x*x₀*y₀^2 - 10*W.a₁^2*x₀^5 + 80*W.a₁^2*x₀^2*y₀^2 + 8*W.a₁*W.a₂*W.a₃*x^2*x₀ + 16*W.a₁*W.a₂*W.a₃*x*x₀^2 - 24*W.a₁*W.a₂*W.a₃*x₀^3 + 64*W.a₁*W.a₂*x*x₀^2*y₀ - 64*W.a₁*W.a₂*x₀^3*y₀ + 4*W.a₁*W.a₃^3*x + 12*W.a₁*W.a₃^3*x₀ + 16*W.a₁*W.a₃^2*x*y₀ + 80*W.a₁*W.a₃^2*x₀*y₀ + 4*W.a₁*W.a₃*W.a₄*x^2 + 8*W.a₁*W.a₃*W.a₄*x*x₀ - 12*W.a₁*W.a₃*W.a₄*x₀^2 - 2*W.a₁*W.a₃*x^4 + 24*W.a₁*W.a₃*x^2*x₀^2 + 8*W.a₁*W.a₃*x*x₀^3 + 16*W.a₁*W.a₃*x*y₀^2 - 30*W.a₁*W.a₃*x₀^4 + 176*W.a₁*W.a₃*x₀*y₀^2 + 32*W.a₁*W.a₄*x*x₀*y₀ - 32*W.a₁*W.a₄*x₀^2*y₀ - 16*W.a₁*x^3*x₀*y₀ + 48*W.a₁*x^2*x₀^2*y₀ + 48*W.a₁*x*x₀^3*y₀ - 80*W.a₁*x₀^4*y₀ + 128*W.a₁*x₀*y₀^3 + 16*W.a₂^2*x^2*x₀^2 - 32*W.a₂^2*x*x₀^3 + 16*W.a₂^2*x₀^4 + 16*W.a₂*W.a₃^2*x*x₀ - 16*W.a₂*W.a₃^2*x₀^2 + 64*W.a₂*W.a₃*x*x₀*y₀ - 64*W.a₂*W.a₃*x₀^2*y₀ + 16*W.a₂*W.a₄*x^2*x₀ - 32*W.a₂*W.a₄*x*x₀^2 + 16*W.a₂*W.a₄*x₀^3 - 8*W.a₂*x^4*x₀ + 32*W.a₂*x^3*x₀^2 - 64*W.a₂*x*x₀^4 + 64*W.a₂*x*x₀*y₀^2 + 40*W.a₂*x₀^5 - 64*W.a₂*x₀^2*y₀^2 + 4*W.a₃^4 + 32*W.a₃^3*y₀ + 8*W.a₃^2*W.a₄*x - 8*W.a₃^2*W.a₄*x₀ - 4*W.a₃^2*x^3 + 12*W.a₃^2*x^2*x₀ + 12*W.a₃^2*x*x₀^2 - 20*W.a₃^2*x₀^3 + 96*W.a₃^2*y₀^2 + 32*W.a₃*W.a₄*x*y₀ - 32*W.a₃*W.a₄*x₀*y₀ - 16*W.a₃*x^3*y₀ + 48*W.a₃*x^2*x₀*y₀ + 48*W.a₃*x*x₀^2*y₀ - 80*W.a₃*x₀^3*y₀ + 128*W.a₃*y₀^3 + 4*W.a₄^2*x^2 - 8*W.a₄^2*x*x₀ + 4*W.a₄^2*x₀^2 - 4*W.a₄*x^4 + 16*W.a₄*x^3*x₀ - 32*W.a₄*x*x₀^3 + 32*W.a₄*x*y₀^2 + 20*W.a₄*x₀^4 - 32*W.a₄*x₀*y₀^2 + x^6 - 6*x^5*x₀ + 3*x^4*x₀^2 + 28*x^3*x₀^3 - 16*x^3*y₀^2 - 21*x^2*x₀^4 + 48*x^2*x₀*y₀^2 - 30*x*x₀^5 + 48*x*x₀^2*y₀^2 + 25*x₀^6 - 80*x₀^3*y₀^2 + 64*y₀^4) * hP
    + (2*W.a₁^4*x^3*x₀ - 4*W.a₁^4*x^2*x₀^2 - 2*W.a₁^4*x*x₀^3 + 2*W.a₁^3*W.a₃*x^3 - 2*W.a₁^3*W.a₃*x^2*x₀ - 14*W.a₁^3*W.a₃*x*x₀^2 - 2*W.a₁^3*W.a₃*x₀^3 + 12*W.a₁^3*x^2*x₀*y₀ - 40*W.a₁^3*x*x₀^2*y₀ - 4*W.a₁^3*x₀^3*y₀ + 16*W.a₁^2*W.a₂*x^3*x₀ - 44*W.a₁^2*W.a₂*x^2*x₀^2 + 24*W.a₁^2*W.a₂*x*x₀^3 + 4*W.a₁^2*W.a₂*x₀^4 + 2*W.a₁^2*W.a₃^2*x^2 - 16*W.a₁^2*W.a₃^2*x*x₀ - 10*W.a₁^2*W.a₃^2*x₀^2 + 12*W.a₁^2*W.a₃*x^2*y₀ - 56*W.a₁^2*W.a₃*x*x₀*y₀ - 52*W.a₁^2*W.a₃*x₀^2*y₀ + 4*W.a₁^2*W.a₄*x^3 - 16*W.a₁^2*W.a₄*x^2*x₀ + 12*W.a₁^2*W.a₄*x*x₀^2 + 12*W.a₁^2*W.a₆*x^2 - 24*W.a₁^2*W.a₆*x*x₀ + 12*W.a₁^2*W.a₆*x₀^2 - 6*W.a₁^2*x^5 + 32*W.a₁^2*x^4*x₀ - 28*W.a₁^2*x^3*x₀^2 - 12*W.a₁^2*x^2*x₀^3 + 12*W.a₁^2*x^2*y₀^2 - 14*W.a₁^2*x*x₀^4 - 40*W.a₁^2*x*x₀*y₀^2 + 28*W.a₁^2*x₀^5 - 68*W.a₁^2*x₀^2*y₀^2 + 8*W.a₁*W.a₂*W.a₃*x^3 - 8*W.a₁*W.a₂*W.a₃*x^2*x₀ - 40*W.a₁*W.a₂*W.a₃*x*x₀^2 + 40*W.a₁*W.a₂*W.a₃*x₀^3 + 48*W.a₁*W.a₂*x^2*x₀*y₀ - 160*W.a₁*W.a₂*x*x₀^2*y₀ + 112*W.a₁*W.a₂*x₀^3*y₀ - 4*W.a₁*W.a₃^3*x - 12*W.a₁*W.a₃^3*x₀ - 16*W.a₁*W.a₃^2*x*y₀ - 80*W.a₁*W.a₃^2*x₀*y₀ - 16*W.a₁*W.a₃*W.a₄*x^2 + 16*W.a₁*W.a₃*W.a₄*x*x₀ + 2*W.a₁*W.a₃*x^4 + 24*W.a₁*W.a₃*x^3*x₀ + 12*W.a₁*W.a₃*x^2*x₀^2 - 152*W.a₁*W.a₃*x*x₀^3 - 16*W.a₁*W.a₃*x*y₀^2 + 114*W.a₁*W.a₃*x₀^4 - 176*W.a₁*W.a₃*x₀*y₀^2 - 32*W.a₁*W.a₄*x*x₀*y₀ + 32*W.a₁*W.a₄*x₀^2*y₀ + 16*W.a₁*x^3*x₀*y₀ + 96*W.a₁*x^2*x₀^2*y₀ - 336*W.a₁*x*x₀^3*y₀ + 224*W.a₁*x₀^4*y₀ - 128*W.a₁*x₀*y₀^3 + 32*W.a₂^2*x^3*x₀ - 112*W.a₂^2*x^2*x₀^2 + 128*W.a₂^2*x*x₀^3 - 48*W.a₂^2*x₀^4 + 24*W.a₂*W.a₃^2*x^2 - 64*W.a₂*W.a₃^2*x*x₀ + 40*W.a₂*W.a₃^2*x₀^2 + 48*W.a₂*W.a₃*x^2*y₀ - 160*W.a₂*W.a₃*x*x₀*y₀ + 112*W.a₂*W.a₃*x₀^2*y₀ + 16*W.a₂*W.a₄*x^3 - 64*W.a₂*W.a₄*x^2*x₀ + 80*W.a₂*W.a₄*x*x₀^2 - 32*W.a₂*W.a₄*x₀^3 + 48*W.a₂*W.a₆*x^2 - 96*W.a₂*W.a₆*x*x₀ + 48*W.a₂*W.a₆*x₀^2 - 24*W.a₂*x^5 + 128*W.a₂*x^4*x₀ - 128*W.a₂*x^3*x₀^2 - 144*W.a₂*x^2*x₀^3 + 48*W.a₂*x^2*y₀^2 + 280*W.a₂*x*x₀^4 - 160*W.a₂*x*x₀*y₀^2 - 112*W.a₂*x₀^5 + 112*W.a₂*x₀^2*y₀^2 - 4*W.a₃^4 - 32*W.a₃^3*y₀ - 8*W.a₃^2*W.a₄*x + 8*W.a₃^2*W.a₄*x₀ + 4*W.a₃^2*x^3 + 60*W.a₃^2*x^2*x₀ - 156*W.a₃^2*x*x₀^2 + 92*W.a₃^2*x₀^3 - 96*W.a₃^2*y₀^2 - 32*W.a₃*W.a₄*x*y₀ + 32*W.a₃*W.a₄*x₀*y₀ + 16*W.a₃*x^3*y₀ + 96*W.a₃*x^2*x₀*y₀ - 336*W.a₃*x*x₀^2*y₀ + 224*W.a₃*x₀^3*y₀ - 128*W.a₃*y₀^3 - 16*W.a₄^2*x^2 + 32*W.a₄^2*x*x₀ - 16*W.a₄^2*x₀^2 + 4*W.a₄*x^4 + 32*W.a₄*x^3*x₀ - 72*W.a₄*x^2*x₀^2 + 32*W.a₄*x*x₀^3 - 32*W.a₄*x*y₀^2 + 4*W.a₄*x₀^4 + 32*W.a₄*x₀*y₀^2 + 144*W.a₆*x^2*x₀ - 288*W.a₆*x*x₀^2 + 144*W.a₆*x₀^3 - 72*x^5*x₀ + 372*x^4*x₀^2 - 624*x^3*x₀^3 + 16*x^3*y₀^2 + 360*x^2*x₀^4 + 96*x^2*x₀*y₀^2 + 24*x*x₀^5 - 336*x*x₀^2*y₀^2 - 60*x₀^6 + 224*x₀^3*y₀^2 - 64*y₀^4) * hQ
    + (2*W.a₁^2*x^3*x₀ - 3*W.a₁^2*x^2*x₀^2 + W.a₁^2*x₀^4 + 2*W.a₁*W.a₃*x^3 - 6*W.a₁*W.a₃*x*x₀^2 + 4*W.a₁*W.a₃*x₀^3 + 8*W.a₂*x^3*x₀ - 12*W.a₂*x^2*x₀^2 + 4*W.a₂*x₀^4 + 3*W.a₃^2*x^2 - 6*W.a₃^2*x*x₀ + 3*W.a₃^2*x₀^2 + 4*W.a₄*x^3 - 12*W.a₄*x*x₀^2 + 8*W.a₄*x₀^3 + 12*W.a₆*x^2 - 24*W.a₆*x*x₀ + 12*W.a₆*x₀^2 - 6*x^5 + 30*x^4*x₀ - 48*x^3*x₀^2 + 36*x^2*x₀^3 - 18*x*x₀^4 + 6*x₀^5) * hΨ

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)


@[simp] lemma veluY_empty (x y : F) : W.veluY ∅ x y = y := by simp [veluY]

lemma veluX_singleton (x₀ y₀ : F) {x : F} (hx : x ≠ x₀) :
    W.veluX {(x₀, y₀)} x = W.veluXNum x₀ y₀ x / (x - x₀) ^ 2 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [veluX, Finset.sum_singleton, veluXNum]
  field_simp
  ring

lemma veluY_singleton (x₀ y₀ : F) {x : F} (y : F) (hx : x ≠ x₀) :
    W.veluY {(x₀, y₀)} x y = W.veluYNum x₀ y₀ x y / (x - x₀) ^ 3 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [veluY, Finset.sum_singleton, veluYNum]
  field_simp

theorem velu_singleton_map_equation {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) (hx : x ≠ x₀) :
    (W.veluQuotient {(x₀, y₀)}).toAffine.Equation
      (W.veluX {(x₀, y₀)} x) (W.veluY {(x₀, y₀)} x y) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key := W.velu_singleton_equation_cleared hP hQ hΨ
  rw [Affine.equation_iff, W.veluX_singleton x₀ y₀ hx, W.veluY_singleton x₀ y₀ y hx]
  simp only [veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆, veluTSum, veluWSum, Finset.sum_singleton]
  field_simp
  linear_combination key

end Field

end WeierstrassCurve
