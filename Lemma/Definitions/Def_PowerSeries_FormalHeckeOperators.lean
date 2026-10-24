import Mathlib

set_option autoImplicit false

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R]

def heckeU (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => coeff (ℓ * n) f
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

@[simp] lemma coeff_heckeU (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeU ℓ f) = coeff (ℓ * n) f := by
  simp [heckeU]

def heckeV (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => if ℓ ∣ n then coeff (n / ℓ) f else 0
  map_add' f g := by ext n; by_cases h : ℓ ∣ n <;> simp [h]
  map_smul' c f := by ext n; by_cases h : ℓ ∣ n <;> simp [h]

@[simp] lemma coeff_heckeV (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeV ℓ f) = if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeV]

lemma heckeU_heckeV (ℓ : ℕ) (hℓ : ℓ ≠ 0) (f : R⟦X⟧) : heckeU ℓ (heckeV ℓ f) = f := by
  ext n
  simp [Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hℓ), Dvd.intro n rfl]

def heckeT (ℓ k : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ :=
  heckeU ℓ + (ℓ : R) ^ (k - 1) • heckeV ℓ

lemma coeff_heckeT (ℓ k n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeT ℓ k f) =
      coeff (ℓ * n) f + (ℓ : R) ^ (k - 1) * if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeT]

end PowerSeries

end
