module

public import Theorem.HahnSeries.ModularUnit
public import Theorem.ModularForm.HeckeOperator
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Def.ModularCurve_EtaQuotient

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped ModularForm MatrixGroups

namespace ModularCurve


public theorem sharpIndex_def (ℓ : ℕ) : sharpIndex ℓ = Nat.gcd (ℓ - 1) 12 := rfl

public theorem sharpExp_def (ℓ : ℕ) : sharpExp ℓ = 24 / sharpIndex ℓ := rfl

public theorem sharpIndex_dvd_twelve (ℓ : ℕ) : sharpIndex ℓ ∣ 12 := Nat.gcd_dvd_right _ _

public theorem sharpIndex_dvd_sub_one (ℓ : ℕ) : sharpIndex ℓ ∣ ℓ - 1 := Nat.gcd_dvd_left _ _

public theorem sharpIndex_pos (ℓ : ℕ) : 0 < sharpIndex ℓ :=
  Nat.pos_of_ne_zero fun h => by simpa [h] using sharpIndex_dvd_twelve ℓ

public theorem sharpIndex_dvd_twentyfour (ℓ : ℕ) : sharpIndex ℓ ∣ 24 :=
  (sharpIndex_dvd_twelve ℓ).trans ⟨2, by norm_num⟩

public theorem sharpExp_mul_sharpIndex (ℓ : ℕ) : sharpExp ℓ * sharpIndex ℓ = 24 :=
  Nat.div_mul_cancel (sharpIndex_dvd_twentyfour ℓ)

public theorem sharpExp_pos (ℓ : ℕ) : 0 < sharpExp ℓ :=
  Nat.pos_of_ne_zero fun h => by simpa [h] using sharpExp_mul_sharpIndex ℓ

public theorem two_dvd_sharpExp (ℓ : ℕ) : 2 ∣ sharpExp ℓ := by
  obtain ⟨c, hc⟩ := sharpIndex_dvd_twelve ℓ
  have hk : 0 < sharpIndex ℓ := sharpIndex_pos ℓ
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => by simp [h] at hc
  refine ⟨c, ?_⟩
  have h24 : 24 = sharpIndex ℓ * (2 * c) :=
    calc (24 : ℕ) = 2 * 12 := by norm_num
      _ = 2 * (sharpIndex ℓ * c) := by rw [← hc]
      _ = sharpIndex ℓ * (2 * c) := by ring
  rw [sharpExp, h24, Nat.mul_div_cancel_left _ hk]

public theorem sharpExp_div_two_mul_two (ℓ : ℕ) : sharpExp ℓ / 2 * 2 = sharpExp ℓ :=
  Nat.div_mul_cancel (two_dvd_sharpExp ℓ)

public theorem two_mul_sharpExp_div_two (ℓ : ℕ) : 2 * (sharpExp ℓ / 2) = sharpExp ℓ :=
  Nat.mul_div_cancel' (two_dvd_sharpExp ℓ)

public theorem sharpIndex_mul_eisensteinNumerator (ℓ : ℕ) :
    sharpIndex ℓ * eisensteinNumerator ℓ = ℓ - 1 := by
  rw [eisensteinNumerator, ← sharpIndex_def, Nat.mul_div_cancel' (sharpIndex_dvd_sub_one ℓ)]

public theorem sharpExp_mul_sub_one (ℓ : ℕ) : sharpExp ℓ * (ℓ - 1) = 24 * eisensteinNumerator ℓ := by
  rw [← sharpIndex_mul_eisensteinNumerator, ← mul_assoc, sharpExp_mul_sharpIndex]


public theorem etaProdPow_def (ℓ : ℕ) :
    etaProdPow ℓ = (etaProd ^ sharpExp ℓ).map (Int.castRingHom ℚ) := rfl

public theorem constantCoeff_etaProdPow (ℓ : ℕ) : PowerSeries.constantCoeff (etaProdPow ℓ) = 1 := by
  rw [etaProdPow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_etaProd, one_pow, map_one]

variable (ℓ : ℕ)


public theorem sharpUnitFun_apply (τ : UpperHalfPlane) :
    sharpUnitFun ℓ τ =
      (η (τ : ℂ) / η ((ModularForm.heckeDiagMatrix ℓ • τ : UpperHalfPlane) : ℂ)) ^ sharpExp ℓ :=
  rfl

section Series

variable [NeZero ℓ]


public theorem sharpUnitSeries_def :
    sharpUnitSeries ℓ = HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) *
      HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ) *
      (qExpand ℚ ℓ (HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ)))⁻¹ := rfl

end Series

end ModularCurve

end
