import Mathlib
import Def.PowerSeries_FormalHeckeOperators

set_option autoImplicit false

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R]


@[simp] lemma coeff_heckeU (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeU ℓ f) = coeff (ℓ * n) f := by
  simp [heckeU]


@[simp] lemma coeff_heckeV (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeV ℓ f) = if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeV]

lemma heckeU_heckeV (ℓ : ℕ) (hℓ : ℓ ≠ 0) (f : R⟦X⟧) : heckeU ℓ (heckeV ℓ f) = f := by
  ext n
  simp [Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hℓ), Dvd.intro n rfl]


lemma coeff_heckeT (ℓ k n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeT ℓ k f) =
      coeff (ℓ * n) f + (ℓ : R) ^ (k - 1) * if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeT]

end PowerSeries

end
