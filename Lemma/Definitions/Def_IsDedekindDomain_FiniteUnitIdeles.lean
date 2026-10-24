import Mathlib

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

def unitIdeles : Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {δ | (∀ v : HeightOneSpectrum R, (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) ∧
    ∀ v : HeightOneSpectrum R, ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' := ⟨fun v => by rw [Units.val_one]; exact one_mem _,
              fun v => by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun v => by rw [Units.val_mul]; exact mul_mem (hx1 v) (hy1 v),
           fun v => by rw [mul_inv, Units.val_mul]; exact mul_mem (hx2 v) (hy2 v)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, fun v => by rw [inv_inv]; exact hx1 v⟩

variable {R K} in
theorem mem_unitIdeles_iff (δ : (FiniteAdeleRing R K)ˣ) :
    δ ∈ unitIdeles R K ↔
      (∀ v : HeightOneSpectrum R, (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v : HeightOneSpectrum R,
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

end IsDedekindDomain.FiniteAdeleRing
