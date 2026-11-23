module

public import Mathlib
public import Theorem.PowerSeries.FormalHeckeOperators

@[expose] public section

set_option autoImplicit false

namespace LaurentSeries

noncomputable def heckeU (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    LaurentSeries R →ₗ[R] LaurentSeries R where
  toFun f := HahnSeries.ofSuppBddBelow (fun n : ℤ => f.coeff (ℓ * n)) (bddBelow_support_coeff_mul f ℓ hℓ)
  map_add' f g := by
    ext n
    simp [HahnSeries.ofSuppBddBelow_coeff]
  map_smul' c f := by
    ext n
    simp [HahnSeries.ofSuppBddBelow_coeff]

end LaurentSeries

end
