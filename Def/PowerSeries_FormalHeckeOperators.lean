import Mathlib

set_option autoImplicit false

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R]

def heckeU (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => coeff (ℓ * n) f
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp


def heckeV (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => if ℓ ∣ n then coeff (n / ℓ) f else 0
  map_add' f g := by ext n; by_cases h : ℓ ∣ n <;> simp [h]
  map_smul' c f := by ext n; by_cases h : ℓ ∣ n <;> simp [h]


def heckeT (ℓ k : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ :=
  heckeU ℓ + (ℓ : R) ^ (k - 1) • heckeV ℓ

end PowerSeries

end
