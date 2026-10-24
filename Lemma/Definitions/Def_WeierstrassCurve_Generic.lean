import Mathlib

set_option autoImplicit false

universe u v

noncomputable section

open MvPolynomial

namespace WeierstrassCurve.Generic

section CommRing

variable (K : Type u) [CommRing K]

def poly : WeierstrassCurve (MvPolynomial (Fin 5) K) :=
  ⟨X 0, X 1, X 2, X 3, X 4⟩

@[simp] theorem poly_a₁ : (poly K).a₁ = X 0 := rfl
@[simp] theorem poly_a₂ : (poly K).a₂ = X 1 := rfl
@[simp] theorem poly_a₃ : (poly K).a₃ = X 2 := rfl
@[simp] theorem poly_a₄ : (poly K).a₄ = X 3 := rfl
@[simp] theorem poly_a₆ : (poly K).a₆ = X 4 := rfl

variable {K}

section coeffs

variable {A : Type v}

def coeffs (W : WeierstrassCurve A) : Fin 5 → A := ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

@[simp] theorem coeffs_zero (W : WeierstrassCurve A) : coeffs W 0 = W.a₁ := rfl
@[simp] theorem coeffs_one (W : WeierstrassCurve A) : coeffs W 1 = W.a₂ := rfl
@[simp] theorem coeffs_two (W : WeierstrassCurve A) : coeffs W 2 = W.a₃ := rfl
@[simp] theorem coeffs_three (W : WeierstrassCurve A) : coeffs W 3 = W.a₄ := rfl
@[simp] theorem coeffs_four (W : WeierstrassCurve A) : coeffs W 4 = W.a₆ := rfl

end coeffs

theorem Δ_poly_map {A : Type v} [CommRing A] (f : MvPolynomial (Fin 5) K →+* A) :
    ((poly K).map f).Δ = f (poly K).Δ :=
  (poly K).map_Δ f

variable {A : Type v} [CommRing A] [Algebra K A]

variable (K) in

def classify (W : WeierstrassCurve A) : MvPolynomial (Fin 5) K →ₐ[K] A :=
  MvPolynomial.aeval (coeffs W)

@[simp] theorem classify_X (W : WeierstrassCurve A) (i : Fin 5) :
    classify K W (X i) = coeffs W i := by
  simp [classify]

@[simp] theorem poly_map_classify (W : WeierstrassCurve A) :
    (poly K).map (classify K W : MvPolynomial (Fin 5) K →+* A) = W := by
  rcases W with ⟨a₁, a₂, a₃, a₄, a₆⟩
  simp [poly, WeierstrassCurve.map, coeffs]

theorem eq_classify_of_poly_map_eq (W : WeierstrassCurve A) (f : MvPolynomial (Fin 5) K →ₐ[K] A)
    (hf : (poly K).map (f : MvPolynomial (Fin 5) K →+* A) = W) : f = classify K W := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [classify_X]
  subst hf
  fin_cases i <;> rfl

variable (K) in

theorem Δ_poly_ne_zero [Nontrivial K] : (poly K).Δ ≠ 0 := by
  intro h

  have h₁ : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve K).Δ = 0 := by
    rw [← poly_map_classify (K := K) (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve K), Δ_poly_map, h,
      map_zero]
  have h₂ : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).Δ = 0 := by
    rw [← poly_map_classify (K := K) (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K), Δ_poly_map, h,
      map_zero]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at h₁ h₂
  have e : (1 : K) = 0 := by linear_combination (-11) * h₂ - 8 * h₁
  exact one_ne_zero e

end CommRing

section Field

variable (K : Type u) [Field K]

abbrev FunctionField : Type u := FractionRing (MvPolynomial (Fin 5) K)

abbrev Closure : Type u := AlgebraicClosure (FunctionField K)

def curve : WeierstrassCurve (Closure K) :=
  (poly K).map (algebraMap (MvPolynomial (Fin 5) K) (Closure K))

theorem curve_def : curve K = (poly K).map (algebraMap (MvPolynomial (Fin 5) K) (Closure K)) := rfl

theorem algebraMap_functionField_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 5) K) (FunctionField K)) :=
  IsFractionRing.injective _ _

theorem algebraMap_closure_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 5) K) (Closure K)) := by
  rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
  exact (algebraMap (FunctionField K) (Closure K)).injective.comp
    (algebraMap_functionField_injective K)

theorem Δ_curve : (curve K).Δ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (poly K).Δ :=
  (poly K).map_Δ _

theorem Δ_curve_ne_zero : (curve K).Δ ≠ 0 := by
  rw [Δ_curve]
  exact (map_ne_zero_iff _ (algebraMap_closure_injective K)).2 (Δ_poly_ne_zero K)

theorem isUnit_Δ_curve : IsUnit (curve K).Δ :=
  (Δ_curve_ne_zero K).isUnit

instance isElliptic_curve : (curve K).IsElliptic := ⟨isUnit_Δ_curve K⟩

@[simp] theorem curve_a₁ : (curve K).a₁ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 0) := rfl
@[simp] theorem curve_a₂ : (curve K).a₂ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 1) := rfl
@[simp] theorem curve_a₃ : (curve K).a₃ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 2) := rfl
@[simp] theorem curve_a₄ : (curve K).a₄ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 3) := rfl
@[simp] theorem curve_a₆ : (curve K).a₆ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 4) := rfl

theorem curve_map_algEquiv (σ : Closure K ≃ₐ[FunctionField K] Closure K) :
    (curve K).map (σ : Closure K →+* Closure K) = curve K := by
  rw [curve_def, WeierstrassCurve.map_map]
  congr 1
  ext x
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
    exact σ.commutes _
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
    exact σ.commutes _

end Field

end WeierstrassCurve.Generic

end
