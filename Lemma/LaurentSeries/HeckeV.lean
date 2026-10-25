import Mathlib
import Lemma.LaurentSeries.HeckeU

set_option autoImplicit false

namespace LaurentSeries

theorem bddBelow_support_coeff_div {R : Type*} [Zero R] (f : LaurentSeries R) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    BddBelow (Function.support fun n : ℤ => if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0) := by
  by_cases hS : (Function.support f.coeff).Nonempty
  · refine ⟨(ℓ : ℤ) * f.isWF_support.min hS, fun n hn => ?_⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    obtain ⟨⟨m, rfl⟩, hm⟩ := hn
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
    rw [Int.mul_ediv_cancel_left _ hℓ0] at hm
    have hmin : f.isWF_support.min hS ≤ m := f.isWF_support.min_le hS hm
    have hℓ1 : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
    nlinarith
  · refine ⟨0, fun n hn => ?_⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    exact absurd ⟨_, hn.2⟩ hS

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

@[simp]
theorem coeff_heckeV (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (f : LaurentSeries R) (n : ℤ) :
    (heckeV R ℓ hℓ f).coeff n = if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0 :=
  HahnSeries.ofSuppBddBelow_coeff _ (bddBelow_support_coeff_div f ℓ hℓ) n

noncomputable def heckeT (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ) :
    LaurentSeries R →ₗ[R] LaurentSeries R :=
  heckeU R ℓ hℓ + ((ℓ : R) ^ (k - 1)) • heckeV R ℓ hℓ

theorem coeff_heckeT (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ) (f : LaurentSeries R) (n : ℤ) :
    (heckeT R ℓ hℓ k f).coeff n =
      f.coeff (ℓ * n) + (ℓ : R) ^ (k - 1) * (if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0) := by
  simp [heckeT, coeff_heckeU, coeff_heckeV]

end LaurentSeries
