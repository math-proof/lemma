module

public import Mathlib
public import Instance.WeierstrassCurve_FunctionFieldQuadratic

public noncomputable section

set_option autoImplicit false

noncomputable section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}


public theorem polyToFunctionField_apply (p : F[X]) :
    polyToFunctionField W p
      = algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing p) := rfl


public theorem algebraMap_smul_one (p : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField (p • (1 : W.CoordinateRing))
      = polyToFunctionField W p := by
  rw [polyToFunctionField_apply, smul, mul_one]
  rfl


public theorem polyToFunctionField_injective : Function.Injective (polyToFunctionField W) := by
  intro p q h
  rw [polyToFunctionField_apply, polyToFunctionField_apply] at h
  have h2 := IsFractionRing.injective W.CoordinateRing W.FunctionField h
  have h0 : (p - q) • (1 : W.CoordinateRing) + (0 : F[X]) • CoordinateRing.mk W Y = 0 := by
    rw [zero_smul, add_zero, sub_smul, ← Algebra.algebraMap_eq_smul_one,
      ← Algebra.algebraMap_eq_smul_one, h2, sub_self]
  exact sub_eq_zero.mp (smul_basis_eq_zero h0).1


public theorem polyToFunctionField_C (c : F) :
    polyToFunctionField W (C c) = algebraMap F W.FunctionField c := by
  rw [polyToFunctionField_apply,
    show algebraMap F[X] W.CoordinateRing (C c) = algebraMap F W.CoordinateRing c from
      (IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing c).symm]
  exact (IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c).symm


public theorem polyToFunctionField_ne_zero {p : F[X]} (hp : p ≠ 0) :
    polyToFunctionField W p ≠ 0 := by
  intro h
  exact hp (polyToFunctionField_injective (by simpa using h))


public theorem algebraMap_smul_basis (p q : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField
        (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Y)
      = polyToFunctionField W p + polyToFunctionField W q
          * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) := by
  rw [map_add, algebraMap_smul_one, smul, map_mul, polyToFunctionField_apply]
  rfl


public theorem Y_image_ne_zero :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) ≠ 0 := by
  have h1 : (CoordinateRing.mk W Y) ≠ 0 := by
    have h2 := YClass_ne_zero (W' := W) 0
    simpa [YClass] using h2
  exact (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr h1


public theorem algebraMap_polynomial_eq_polyToFunctionField :
    algebraMap F[X] W.FunctionField = polyToFunctionField W :=
  IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField


public theorem algebraMap_polynomial_injective :
    Function.Injective (algebraMap F[X] W.FunctionField) := by
  rw [algebraMap_polynomial_eq_polyToFunctionField]
  exact polyToFunctionField_injective

variable (W) in


@[simp]
public theorem ratFuncToFunctionField_algebraMap (p : F[X]) :
    ratFuncToFunctionField W (algebraMap F[X] (RatFunc F) p)
      = algebraMap F[X] W.FunctionField p :=
  IsFractionRing.lift_algebraMap algebraMap_polynomial_injective p

variable (W) in


public theorem weierstrassQuadratic_sub_degree_lt :
    (C (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) * X
      - C (algebraMap F[X] (RatFunc F)
        (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))).degree < ((2 : ℕ) : WithBot ℕ) := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg]
  exact lt_of_le_of_lt Polynomial.degree_linear_le (by exact_mod_cast Nat.one_lt_two)


public theorem weierstrassQuadratic_monic : (weierstrassQuadratic W).Monic :=
  monic_X_pow_add weierstrassQuadratic_sub_degree_lt


public theorem yCoord_relation :
    yCoord W * yCoord W
      = polyToFunctionField W (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
        - polyToFunctionField W (C W.a₁ * X + C W.a₃) * yCoord W := by
  have h1 := smul_basis_mul_Y (W' := W) 0 1
  rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at h1
  have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) h1
  rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
  exact h2


public theorem aeval_yCoord_weierstrassQuadratic :
    Polynomial.aeval (yCoord W) (weierstrassQuadratic W) = 0 := by
  have hc : ∀ p : F[X],
      algebraMap (RatFunc F) W.FunctionField (algebraMap F[X] (RatFunc F) p)
        = polyToFunctionField W p := fun p => by
    rw [← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
      algebraMap_polynomial_eq_polyToFunctionField]
  simp only [weierstrassQuadratic, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, hc]
  rw [sq]
  have hrel := yCoord_relation (W := W)
  simp only [map_add, map_mul, map_pow] at hrel ⊢
  linear_combination hrel


public theorem isIntegral_yCoord : _root_.IsIntegral (RatFunc F) (yCoord W) :=
  ⟨weierstrassQuadratic W, weierstrassQuadratic_monic, by
    rw [← Polynomial.aeval_def]; exact aeval_yCoord_weierstrassQuadratic⟩

end WeierstrassCurve.Affine

end
