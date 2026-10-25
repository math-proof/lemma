import Mathlib
import Lemma.WeierstrassCurve.VeluPointMap

open Polynomial

namespace WeierstrassCurve

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private lemma veluY_summand_negY (x y : F) (Q : F × F) :
    W.veluU Q.1 Q.2 * (2 * W.toAffine.negY x y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
      + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + W.toAffine.negY x y - Q.2) / (x - Q.1) ^ 2
      + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2
    = W.a₁ * (W.veluT Q.1 Q.2 / (x - Q.1) + W.veluU Q.1 Q.2 / (x - Q.1) ^ 2)
      - (W.veluU Q.1 Q.2 * (2 * y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
        + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + y - Q.2) / (x - Q.1) ^ 2
        + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2) := by
  rcases eq_or_ne x Q.1 with h | h
  · simp [h, sub_self]
  · have hd : x - Q.1 ≠ 0 := sub_ne_zero.mpr h
    simp only [veluT, veluU, veluGx, veluGy, Affine.negY]
    field_simp
    ring

lemma veluY_negY (S : Finset (F × F)) (x y : F) :
    W.veluY S x (W.toAffine.negY x y)
      = (W.veluQuotient S).toAffine.negY (W.veluX S x) (W.veluY S x y) := by
  simp only [veluY, veluX]
  rw [Finset.sum_congr rfl fun Q _ => W.veluY_summand_negY x y Q,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Affine.negY, veluQuotient_a₁, veluQuotient_a₃]
  ring

variable {W} in

theorem velu_singleton_map_nonsingular {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) (hx : x ≠ x₀)
    (hΔ : (W.veluQuotient {(x₀, y₀)}).Δ ≠ 0) :
    (W.veluQuotient {(x₀, y₀)}).toAffine.Nonsingular
      (W.veluX {(x₀, y₀)} x) (W.veluY {(x₀, y₀)} x y) :=
  ((W.veluQuotient {(x₀, y₀)}).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    (W.velu_singleton_map_equation hP hQ hΨ hx)

private lemma some_congr {W' : Affine F} {x y₁ y₂ : F} {h₁ : W'.Nonsingular x y₁}
    {h₂ : W'.Nonsingular x y₂} (hy : y₁ = y₂) :
    Affine.Point.some x y₁ h₁ = Affine.Point.some x y₂ h₂ := by
  subst hy; rfl

variable {W} in
open scoped Classical in

noncomputable def veluPointMap3 {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) (hΔ : (W.veluQuotient {(x₀, y₀)}).Δ ≠ 0) :
    W.toAffine.Point → (W.veluQuotient {(x₀, y₀)}).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x = x₀ then .zero
    else .some _ _ (velu_singleton_map_nonsingular h.1 hQ hΨ hx hΔ)

variable {W}
variable {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀) (hΨ : (W.Ψ₃).eval x₀ = 0)
  (hΔ : (W.veluQuotient {(x₀, y₀)}).Δ ≠ 0)

@[simp] lemma veluPointMap3_zero : veluPointMap3 hQ hΨ hΔ .zero = .zero := rfl

lemma veluPointMap3_some_of_eq {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = x₀) :
    veluPointMap3 hQ hΨ hΔ (.some x y h) = .zero := by
  simp only [veluPointMap3]
  exact dif_pos hx

lemma veluPointMap3_some_of_ne {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x ≠ x₀) :
    veluPointMap3 hQ hΨ hΔ (.some x y h)
      = .some _ _ (velu_singleton_map_nonsingular h.1 hQ hΨ hx hΔ) := by
  simp only [veluPointMap3]
  exact dif_neg hx

lemma veluPointMap3_neg (P : W.toAffine.Point) :
    veluPointMap3 hQ hΨ hΔ (-P) = -(veluPointMap3 hQ hΨ hΔ P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x = x₀
    · rw [veluPointMap3_some_of_eq hQ hΨ hΔ _ hx, veluPointMap3_some_of_eq hQ hΨ hΔ h hx]
      rfl
    · rw [veluPointMap3_some_of_ne hQ hΨ hΔ _ hx, veluPointMap3_some_of_ne hQ hΨ hΔ h hx,
        Affine.Point.neg_some]
      exact some_congr (W.veluY_negY {(x₀, y₀)} x y)

end Field

end WeierstrassCurve
