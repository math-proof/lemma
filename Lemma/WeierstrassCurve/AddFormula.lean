import Mathlib

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

section evalLemmas

lemma eval_Ψ₂Sq (x : F) : W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [Ψ₂Sq]

lemma eval_Φ_two (x : F) :
    (W.Φ 2).eval x = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  simp [Φ_two]

lemma sq_sub_negY_eq_eval_Ψ₂Sq {x y : F} (h : W.Equation x y) :
    (y - W.negY x y) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [equation_iff] at h
  rw [eval_Ψ₂Sq, negY, b₂, b₄, b₆]
  linear_combination 4 * h

end evalLemmas

section slope

variable [DecidableEq F]

lemma addX_mul_sq_of_X_ne {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [slope_of_X_ne hx, addX]
  field_simp
  ring

theorem addX_add_addX_negY_mul_sq {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) +
        W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))) * (x₁ - x₂) ^ 2 =
      2 * (x₁ * x₂) * (x₁ + x₂) + W.b₂ * (x₁ * x₂) + W.b₄ * (x₁ + x₂) + W.b₆ := by
    have e₁ := addX_mul_sq_of_X_ne (W := W) y₁ y₂ hx
    have e₂ := addX_mul_sq_of_X_ne (W := W) y₁ (W.negY x₂ y₂) hx
    rw [equation_iff] at h₁ h₂
    rw [add_mul, e₁, e₂, negY, b₂, b₄, b₆]
    linear_combination 2 * h₁ + 2 * h₂

theorem addX_mul_addX_negY_mul_sq {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) *
        W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) * (x₁ - x₂) ^ 2 =
      (x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈ := by
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hd2 : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 hd
    have e₁ := addX_mul_sq_of_X_ne (W := W) y₁ y₂ hx
    have e₂ := addX_mul_sq_of_X_ne (W := W) y₁ (W.negY x₂ y₂) hx

    have key : ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
          (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) *
        ((y₁ - W.negY x₂ y₂) ^ 2 + W.a₁ * (y₁ - W.negY x₂ y₂) * (x₁ - x₂) -
          (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) =
        ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) * (x₁ - x₂) ^ 2 := by
      rw [equation_iff] at h₁ h₂
      rw [negY, b₄, b₆, b₈]
      linear_combination
        (W.a₁ ^ 2 * x₁ * x₂ - W.a₁ ^ 2 * x₂ ^ 2 + W.a₁ * W.a₃ * x₁ - W.a₁ * W.a₃ * x₂ +
            W.a₁ * x₁ * y₁ - 2 * W.a₁ * x₂ * y₂ - W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ -
            2 * W.a₂ * x₂ ^ 2 + W.a₃ * y₁ - 2 * W.a₃ * y₂ + W.a₄ * x₁ + W.a₆ - x₁ ^ 3 +
            2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 2 * x₂ ^ 3 + y₁ ^ 2 - 2 * y₂ ^ 2) * h₁ +
        (-W.a₁ ^ 2 * x₁ ^ 2 + W.a₁ ^ 2 * x₁ * x₂ - W.a₁ * W.a₃ * x₁ + W.a₁ * W.a₃ * x₂ +
            W.a₁ * x₂ * y₂ - 4 * W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ - W.a₂ * x₂ ^ 2 +
            W.a₃ * y₂ - 2 * W.a₄ * x₁ + W.a₄ * x₂ - W.a₆ - 4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ +
            2 * x₁ * x₂ ^ 2 - x₂ ^ 3 + y₂ ^ 2) * h₂
    apply mul_left_cancel₀ hd2
    calc (x₁ - x₂) ^ 2 * (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) *
            W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) * (x₁ - x₂) ^ 2)
        = (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2) *
            (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) * (x₁ - x₂) ^ 2) := by ring
      _ = ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
              (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) *
            ((y₁ - W.negY x₂ y₂) ^ 2 + W.a₁ * (y₁ - W.negY x₂ y₂) * (x₁ - x₂) -
              (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) := by rw [e₁, e₂]
      _ = ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) * (x₁ - x₂) ^ 2 := key
      _ = (x₁ - x₂) ^ 2 *
            ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) := by ring

lemma addX_self_mul_sq_of_Y_ne {x₁ y₁ : F} (hy : y₁ ≠ W.negY x₁ y₁) :
    W.addX x₁ x₁ (W.slope x₁ x₁ y₁ y₁) * (y₁ - W.negY x₁ y₁) ^ 2 =
      (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) ^ 2 +
        W.a₁ * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) * (y₁ - W.negY x₁ y₁) -
        (W.a₂ + x₁ + x₁) * (y₁ - W.negY x₁ y₁) ^ 2 := by
  have hψ : y₁ - W.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
  rw [slope_of_Y_ne rfl hy, addX]
  field_simp
  ring

theorem addX_self_mul_Ψ₂Sq {x₁ y₁ : F} (h₁ : W.Equation x₁ y₁) (hy : y₁ ≠ W.negY x₁ y₁) :
    W.addX x₁ x₁ (W.slope x₁ x₁ y₁ y₁) * W.Ψ₂Sq.eval x₁ = (W.Φ 2).eval x₁ := by
  rw [← sq_sub_negY_eq_eval_Ψ₂Sq h₁, addX_self_mul_sq_of_Y_ne hy, eval_Φ_two]
  rw [equation_iff] at h₁
  rw [negY, b₄, b₆, b₈]
  linear_combination (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x₁) * h₁

theorem addX_self_mul_ΨSq_two {x₁ y₁ : F} (h₁ : W.Equation x₁ y₁) (hy : y₁ ≠ W.negY x₁ y₁) :
    W.addX x₁ x₁ (W.slope x₁ x₁ y₁ y₁) * (W.ΨSq 2).eval x₁ = (W.Φ 2).eval x₁ := by
  rw [ΨSq_two]
  exact addX_self_mul_Ψ₂Sq h₁ hy

end slope

end WeierstrassCurve.Affine
