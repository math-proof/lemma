import Lemma.Definitions.Def_ModularCurve_X0

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

def IsMonicOfOrder (f : LaurentSeries ℚ) (m : ℤ) : Prop :=
  f.order = m ∧ f.leadingCoeff = 1

namespace IsMonicOfOrder

theorem ne_zero {f : LaurentSeries ℚ} {m : ℤ} (h : IsMonicOfOrder f m) : f ≠ 0 :=
  HahnSeries.leadingCoeff_ne_zero.mp (by rw [h.2]; exact one_ne_zero)

theorem coeff_self {f : LaurentSeries ℚ} {m : ℤ} (h : IsMonicOfOrder f m) :
    f.coeff m = 1 := by
  have h2 := h.2
  rwa [HahnSeries.leadingCoeff_eq, h.1] at h2

theorem coeff_of_lt {f : LaurentSeries ℚ} {m k : ℤ} (h : IsMonicOfOrder f m) (hk : k < m) :
    f.coeff k = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_order (h.1 ▸ hk)

theorem single (m : ℤ) : IsMonicOfOrder (HahnSeries.single m (1 : ℚ)) m := by
  refine ⟨HahnSeries.order_single one_ne_zero, ?_⟩
  rw [HahnSeries.leadingCoeff_eq, HahnSeries.order_single one_ne_zero,
    HahnSeries.coeff_single_same]

theorem ofPowerSeries {U : PowerSeries ℚ} (hU : PowerSeries.constantCoeff U = 1) :
    IsMonicOfOrder (HahnSeries.ofPowerSeries ℤ ℚ U) 0 := by
  have hcoeff0 : (HahnSeries.ofPowerSeries ℤ ℚ U).coeff (0 : ℤ) = 1 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff, hU]
  have hne0 : (HahnSeries.ofPowerSeries ℤ ℚ U).coeff (0 : ℤ) ≠ 0 := by
    rw [hcoeff0]; exact one_ne_zero
  have hne : HahnSeries.ofPowerSeries ℤ ℚ U ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hne0
  have horder : (HahnSeries.ofPowerSeries ℤ ℚ U).order = 0 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hne0) ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hne (HahnSeries.coeff_order_eq_zero.mp
      (ModularCurve.ofPowerSeries_coeff_of_neg U hlt))
  exact ⟨horder, by rw [HahnSeries.leadingCoeff_eq, horder, hcoeff0]⟩

theorem mul {f g : LaurentSeries ℚ} {m n : ℤ} (hf : IsMonicOfOrder f m)
    (hg : IsMonicOfOrder g n) : IsMonicOfOrder (f * g) (m + n) := by
  have h1 : f.leadingCoeff * g.leadingCoeff ≠ 0 := by
    rw [hf.2, hg.2, one_mul]; exact one_ne_zero
  refine ⟨?_, ?_⟩
  · rw [HahnSeries.order_mul_of_ne_zero h1, hf.1, hg.1]
  · rw [HahnSeries.leadingCoeff_mul_of_ne_zero h1, hf.2, hg.2, one_mul]

theorem of_mul_right {f g : LaurentSeries ℚ} {k n : ℤ} (hfg : IsMonicOfOrder (f * g) k)
    (hg : IsMonicOfOrder g n) : IsMonicOfOrder f (k - n) := by

  have hlc : f.leadingCoeff = 1 := by
    have h := HahnSeries.leadingCoeff_mul f g
    rw [hfg.2, hg.2, mul_one] at h
    exact h.symm
  have h1 : f.leadingCoeff * g.leadingCoeff ≠ 0 := by
    rw [hlc, hg.2, one_mul]; exact one_ne_zero
  refine ⟨?_, hlc⟩
  have h := HahnSeries.order_mul_of_ne_zero h1
  rw [hfg.1, hg.1] at h
  omega

theorem qExpand {f : LaurentSeries ℚ} {m : ℤ} (p : ℕ) [NeZero p] (hf : IsMonicOfOrder f m) :
    IsMonicOfOrder (ModularCurve.qExpand ℚ p f) ((p : ℤ) * m) := by
  have hcoeff : (ModularCurve.qExpand ℚ p f).coeff ((p : ℤ) * m) = 1 := by
    rw [qExpand_coeff_mul]; exact hf.coeff_self
  have hcoeff' : (ModularCurve.qExpand ℚ p f).coeff ((p : ℤ) * m) ≠ 0 := by
    rw [hcoeff]; exact one_ne_zero
  have hne : ModularCurve.qExpand ℚ p f ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hcoeff'

  have hbelow : ∀ k : ℤ, k < (p : ℤ) * m → (ModularCurve.qExpand ℚ p f).coeff k = 0 := by
    intro k hk
    by_cases hdvd : (p : ℤ) ∣ k
    · obtain ⟨j, rfl⟩ := hdvd
      rw [qExpand_coeff_mul]
      refine hf.coeff_of_lt ?_
      have hp : (0 : ℤ) < (p : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
      exact lt_of_mul_lt_mul_left hk hp.le
    · exact qExpand_coeff_of_not_dvd p f hdvd
  have horder : (ModularCurve.qExpand ℚ p f).order = (p : ℤ) * m := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcoeff') ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hne (HahnSeries.coeff_order_eq_zero.mp (hbelow _ hlt))
  exact ⟨horder, by rw [HahnSeries.leadingCoeff_eq, horder, hcoeff]⟩

end IsMonicOfOrder

section ModularUnit

def dedekindEtaUnitQ : PowerSeries ℚ := dedekindEtaUnit.map (Int.castRingHom ℚ)

@[simp]
theorem constantCoeff_dedekindEtaUnitQ : PowerSeries.constantCoeff dedekindEtaUnitQ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, dedekindEtaUnitQ, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnit]
  simp

def deltaSeries : LaurentSeries ℚ :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ dedekindEtaUnitQ

theorem isMonicOfOrder_deltaSeries : IsMonicOfOrder deltaSeries 1 := by
  have h := (IsMonicOfOrder.single (1 : ℤ)).mul
    (IsMonicOfOrder.ofPowerSeries constantCoeff_dedekindEtaUnitQ)
  rwa [add_zero] at h

theorem deltaSeries_ne_zero : deltaSeries ≠ 0 := isMonicOfOrder_deltaSeries.ne_zero

variable (p : ℕ) [NeZero p]

def deltaSeriesN : LaurentSeries ℚ := qExpand ℚ p deltaSeries

theorem isMonicOfOrder_deltaSeriesN : IsMonicOfOrder (deltaSeriesN p) (p : ℤ) := by
  have h := isMonicOfOrder_deltaSeries.qExpand p
  rwa [mul_one] at h

theorem deltaSeriesN_ne_zero : deltaSeriesN p ≠ 0 := (isMonicOfOrder_deltaSeriesN p).ne_zero

def modularUnitSeries : LaurentSeries ℚ := deltaSeries * (deltaSeriesN p)⁻¹

theorem modularUnitSeries_mul_deltaSeriesN :
    modularUnitSeries p * deltaSeriesN p = deltaSeries := by
  rw [modularUnitSeries, mul_assoc, inv_mul_cancel₀ (deltaSeriesN_ne_zero p), mul_one]

theorem isMonicOfOrder_modularUnitSeries : IsMonicOfOrder (modularUnitSeries p) (1 - p) := by
  refine IsMonicOfOrder.of_mul_right ?_ (isMonicOfOrder_deltaSeriesN p)
  rw [modularUnitSeries_mul_deltaSeriesN]
  exact isMonicOfOrder_deltaSeries

theorem modularUnitSeries_ne_zero : modularUnitSeries p ≠ 0 :=
  (isMonicOfOrder_modularUnitSeries p).ne_zero

theorem order_modularUnitSeries : (modularUnitSeries p).order = 1 - (p : ℤ) :=
  (isMonicOfOrder_modularUnitSeries p).1

theorem coeff_modularUnitSeries_self : (modularUnitSeries p).coeff (1 - (p : ℤ)) = 1 :=
  (isMonicOfOrder_modularUnitSeries p).coeff_self

theorem coeff_modularUnitSeries_of_lt {k : ℤ} (hk : k < 1 - (p : ℤ)) :
    (modularUnitSeries p).coeff k = 0 :=
  (isMonicOfOrder_modularUnitSeries p).coeff_of_lt hk

theorem deltaSeriesN_one : deltaSeriesN 1 = deltaSeries :=
  qExpand_one_apply deltaSeries

theorem modularUnitSeries_one : modularUnitSeries 1 = 1 := by
  rw [modularUnitSeries, deltaSeriesN_one, mul_inv_cancel₀ deltaSeries_ne_zero]

theorem deltaSeriesN_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] :
    deltaSeriesN (a * b) = qExpand ℚ a (deltaSeriesN b) := by
  rw [deltaSeriesN, deltaSeriesN, qExpand_qExpand]

theorem modularUnitSeries_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] :
    modularUnitSeries (a * b) = modularUnitSeries a * qExpand ℚ a (modularUnitSeries b) := by
  rw [modularUnitSeries, modularUnitSeries, modularUnitSeries, map_mul, map_inv₀,
    ← deltaSeriesN_mul, ← deltaSeriesN, mul_assoc, ← mul_assoc (deltaSeriesN a)⁻¹,
    inv_mul_cancel₀ (deltaSeriesN_ne_zero a), one_mul]

end ModularUnit

def eisensteinNumerator (p : ℕ) : ℕ := (p - 1) / Nat.gcd (p - 1) 12

theorem eisensteinNumerator_dvd (p : ℕ) : eisensteinNumerator p ∣ p - 1 :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

@[simp] theorem eisensteinNumerator_five : eisensteinNumerator 5 = 1 := by decide
@[simp] theorem eisensteinNumerator_seven : eisensteinNumerator 7 = 1 := by decide
@[simp] theorem eisensteinNumerator_thirteen : eisensteinNumerator 13 = 1 := by decide

@[simp] theorem eisensteinNumerator_eleven : eisensteinNumerator 11 = 5 := by decide
@[simp] theorem eisensteinNumerator_seventeen : eisensteinNumerator 17 = 4 := by decide
@[simp] theorem eisensteinNumerator_nineteen : eisensteinNumerator 19 = 3 := by decide
@[simp] theorem eisensteinNumerator_twentythree : eisensteinNumerator 23 = 11 := by decide

end ModularCurve

end
