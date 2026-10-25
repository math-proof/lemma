import Lemma.ModularCurve.JqCoeff
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Instance.ModularCurve_TateFormal
import Def.ModularCurve_TateFormal

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve


theorem twelve_mul_tateB (d : ℕ) : 12 * tateB d = 5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5 := by
  have key : ∀ c : ℤ, (12 : ℤ) ∣ 5 * c ^ 3 + 7 * c ^ 5 := by
    intro c
    have hr : c % 12 ≡ c [ZMOD 12] := Int.mod_modEq c 12
    have hcong : 5 * (c % 12) ^ 3 + 7 * (c % 12) ^ 5 ≡ 5 * c ^ 3 + 7 * c ^ 5 [ZMOD 12] :=
      ((hr.pow 3).mul_left 5).add ((hr.pow 5).mul_left 7)
    have h12 : c % 12 = 0 ∨ c % 12 = 1 ∨ c % 12 = 2 ∨ c % 12 = 3 ∨ c % 12 = 4 ∨ c % 12 = 5 ∨
        c % 12 = 6 ∨ c % 12 = 7 ∨ c % 12 = 8 ∨ c % 12 = 9 ∨ c % 12 = 10 ∨ c % 12 = 11 := by
      omega
    have hres : 5 * (c % 12) ^ 3 + 7 * (c % 12) ^ 5 ≡ 0 [ZMOD 12] := by
      rcases h12 with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    exact Int.modEq_zero_iff_dvd.mp (hcong.symm.trans hres)
  rw [tateB]
  exact Int.mul_ediv_cancel' (key _)


theorem coeff_tateA4 (n : ℕ) :
    PowerSeries.coeff n tateA4 = -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3) :=
  PowerSeries.coeff_mk n _

theorem coeff_tateA6 (n : ℕ) :
    PowerSeries.coeff n tateA6 = -∑ d ∈ n.divisors, tateB d :=
  PowerSeries.coeff_mk n _

theorem coeff_zero_tateA4 : PowerSeries.coeff 0 tateA4 = 0 := by
  rw [coeff_tateA4, Nat.divisors_zero, Finset.sum_empty, neg_zero]

theorem coeff_zero_tateA6 : PowerSeries.coeff 0 tateA6 = 0 := by
  rw [coeff_tateA6, Nat.divisors_zero, Finset.sum_empty, neg_zero]

theorem constantCoeff_tateA4 : PowerSeries.constantCoeff tateA4 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_tateA4

theorem constantCoeff_tateA6 : PowerSeries.constantCoeff tateA6 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_tateA6

theorem constantCoeff_eisenstein6 : PowerSeries.constantCoeff eisenstein6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein6]

theorem coeff_one_tateA4 : PowerSeries.coeff 1 tateA4 = -5 := by
  rw [coeff_tateA4, Nat.divisors_one, Finset.sum_singleton]
  norm_num

theorem coeff_one_tateA6 : PowerSeries.coeff 1 tateA6 = -1 := by
  have h : tateB 1 = 1 := by norm_num [tateB]
  rw [coeff_tateA6, Nat.divisors_one, Finset.sum_singleton, h]


@[simp] theorem tatePowerSeries_a₁ : tatePowerSeries.a₁ = 1 := rfl
@[simp] theorem tatePowerSeries_a₂ : tatePowerSeries.a₂ = 0 := rfl
@[simp] theorem tatePowerSeries_a₃ : tatePowerSeries.a₃ = 0 := rfl
@[simp] theorem tatePowerSeries_a₄ : tatePowerSeries.a₄ = tateA4 := rfl
@[simp] theorem tatePowerSeries_a₆ : tatePowerSeries.a₆ = tateA6 := rfl


theorem laurentOfInt_apply (K : Type*) [CommRing K] (f : PowerSeries ℤ) :
    laurentOfInt K f = HahnSeries.ofPowerSeries ℤ K (f.map (Int.castRingHom K)) := rfl


@[simp] theorem tateLaurent_a₄ (K : Type*) [CommRing K] :
    (tateLaurent K).a₄ = laurentOfInt K tateA4 := rfl

@[simp] theorem tateLaurent_a₆ (K : Type*) [CommRing K] :
    (tateLaurent K).a₆ = laurentOfInt K tateA6 := rfl

end ModularCurve

end
