import Mathlib
import Lemma.PowerSeries.FormalHeckeOperators

set_option autoImplicit false

namespace LaurentSeries

theorem bddBelow_support_coeff_mul {R : Type*} [Zero R] (f : LaurentSeries R) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    BddBelow (Function.support fun n : ℤ => f.coeff (ℓ * n)) := by
  by_cases hS : (Function.support f.coeff).Nonempty
  · refine ⟨min (f.isWF_support.min hS) 0, fun n hn => ?_⟩
    have hmem : (ℓ : ℤ) * n ∈ Function.support f.coeff := hn
    have hmin : f.isWF_support.min hS ≤ (ℓ : ℤ) * n := f.isWF_support.min_le hS hmem
    by_cases hn0 : 0 ≤ n
    · exact le_trans (min_le_right _ _) hn0
    · have hℓ1 : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
      have hle : (ℓ : ℤ) * n ≤ n := by nlinarith
      exact le_trans (min_le_left _ _) (hmin.trans hle)
  · refine ⟨0, fun n hn => ?_⟩
    exact absurd ⟨(ℓ : ℤ) * n, hn⟩ hS

noncomputable def heckeU (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    LaurentSeries R →ₗ[R] LaurentSeries R where
  toFun f := HahnSeries.ofSuppBddBelow (fun n : ℤ => f.coeff (ℓ * n)) (bddBelow_support_coeff_mul f ℓ hℓ)
  map_add' f g := by
    ext n
    simp [HahnSeries.ofSuppBddBelow_coeff]
  map_smul' c f := by
    ext n
    simp [HahnSeries.ofSuppBddBelow_coeff]

@[simp]
theorem coeff_heckeU (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (f : LaurentSeries R) (n : ℤ) :
    (heckeU R ℓ hℓ f).coeff n = f.coeff (ℓ * n) :=
  HahnSeries.ofSuppBddBelow_coeff _ (bddBelow_support_coeff_mul f ℓ hℓ) n

theorem heckeU_ofPowerSeries (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (φ : PowerSeries R) :
    heckeU R ℓ hℓ (φ : LaurentSeries R) = ((PowerSeries.heckeU ℓ φ : PowerSeries R) : LaurentSeries R) := by
  ext n
  rw [coeff_heckeU, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h1 : ¬ (ℓ : ℤ) * (m : ℤ) < 0 := not_lt.mpr (by positivity)
    have h2 : ¬ (m : ℤ) < 0 := not_lt.mpr hn
    rw [if_neg h1, if_neg h2, PowerSeries.coeff_heckeU]
    congr 1
  · have h1 : (ℓ : ℤ) * n < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hℓ) hn
    rw [if_pos h1, if_pos hn]

end LaurentSeries
