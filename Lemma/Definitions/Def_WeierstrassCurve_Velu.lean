import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluGx (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

def veluGy (x y : R) : R := -(2 * y + W.a₁ * x + W.a₃)

def veluT (x y : R) : R := 2 * W.veluGx x y - W.a₁ * W.veluGy x y

def veluU (x y : R) : R := W.veluGy x y ^ 2

def veluW (x y : R) : R := W.veluU x y + x * W.veluT x y

lemma veluT_eq (x y : R) : W.veluT x y = 6 * x ^ 2 + W.b₂ * x + W.b₄ := by
  simp only [veluT, veluGx, veluGy, b₂, b₄]; ring

lemma veluU_eq_Ψ₂Sq_eval {x y : R} (h : W.toAffine.Equation x y) :
    W.veluU x y = W.Ψ₂Sq.eval x := by
  rw [Affine.equation_iff] at h
  simp only [veluU, veluGy, Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * h

lemma veluGy_negY (x y : R) : W.veluGy x (W.toAffine.negY x y) = -W.veluGy x y := by
  simp only [veluGy, Affine.negY]; ring

lemma veluT_negY (x y : R) : W.veluT x (W.toAffine.negY x y) = W.veluT x y := by
  simp only [veluT_eq]

lemma veluU_negY (x y : R) : W.veluU x (W.toAffine.negY x y) = W.veluU x y := by
  simp only [veluU, veluGy, Affine.negY]; ring

lemma veluW_negY (x y : R) : W.veluW x (W.toAffine.negY x y) = W.veluW x y := by
  simp only [veluW, veluU_negY, veluT_negY]

lemma veluGy_eq_zero_of_negY_eq {x y : R} (h : W.toAffine.negY x y = y) :
    W.veluGy x y = 0 := by
  have : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    have := h
    simp only [Affine.negY] at this
    linear_combination -this
  simp [veluGy, this]

variable (S : Finset (R × R))

def veluTSum : R := ∑ P ∈ S, W.veluT P.1 P.2

def veluWSum : R := ∑ P ∈ S, W.veluW P.1 P.2

@[simp] lemma veluTSum_empty : W.veluTSum ∅ = 0 := by simp [veluTSum]

@[simp] lemma veluWSum_empty : W.veluWSum ∅ = 0 := by simp [veluWSum]

def veluQuotient : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluTSum S
  a₆ := W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S

@[simp] lemma veluQuotient_a₁ : (W.veluQuotient S).a₁ = W.a₁ := rfl
@[simp] lemma veluQuotient_a₂ : (W.veluQuotient S).a₂ = W.a₂ := rfl
@[simp] lemma veluQuotient_a₃ : (W.veluQuotient S).a₃ = W.a₃ := rfl
lemma veluQuotient_a₄ : (W.veluQuotient S).a₄ = W.a₄ - 5 * W.veluTSum S := rfl
lemma veluQuotient_a₆ :
    (W.veluQuotient S).a₆ = W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S := rfl

@[simp] lemma veluQuotient_empty : W.veluQuotient ∅ = W := by
  ext <;> simp [veluQuotient]

lemma veluQuotient_b₂ : (W.veluQuotient S).b₂ = W.b₂ := by
  simp [b₂]

lemma veluQuotient_b₄ : (W.veluQuotient S).b₄ = W.b₄ - 10 * W.veluTSum S := by
  simp only [b₄, veluQuotient_a₃, veluQuotient_a₁, veluQuotient_a₄]; ring

lemma veluQuotient_b₆ :
    (W.veluQuotient S).b₆ = W.b₆ - 4 * W.b₂ * W.veluTSum S - 28 * W.veluWSum S := by
  simp only [b₆, b₂, veluQuotient_a₃, veluQuotient_a₆]; ring

lemma veluQuotient_b₈ :
    (W.veluQuotient S).b₈ = W.b₈ + (5 * W.b₄ - W.b₂ ^ 2) * W.veluTSum S
      - 7 * W.b₂ * W.veluWSum S - 25 * W.veluTSum S ^ 2 := by
  simp only [b₈, b₂, b₄, veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆]
  ring

structure IsVeluSet : Prop where
  equation : ∀ P ∈ S, W.toAffine.Equation P.1 P.2

lemma isVeluSet_empty : W.IsVeluSet ∅ := ⟨by simp⟩

end WeierstrassCurve
