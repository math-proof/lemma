module

public import Mathlib
public import Def.ModularCurve_HeckeU

@[expose] public section

set_option autoImplicit false

namespace LaurentSeries

noncomputable def heckeV (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    LaurentSeries R →ₗ[R] LaurentSeries R where
  toFun f := HahnSeries.ofSuppBddBelow (fun n : ℤ => if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0)
    (bddBelow_support_coeff_div f ℓ hℓ)
  map_add' f g := by
    ext n
    by_cases h : (ℓ : ℤ) ∣ n <;> simp [HahnSeries.ofSuppBddBelow_coeff, h]
  map_smul' c f := by
    ext n
    by_cases h : (ℓ : ℤ) ∣ n <;> simp [HahnSeries.ofSuppBddBelow_coeff, h]

noncomputable def heckeT (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ) :
    LaurentSeries R →ₗ[R] LaurentSeries R :=
  heckeU R ℓ hℓ + ((ℓ : R) ^ (k - 1)) • heckeV R ℓ hℓ

end LaurentSeries

end
