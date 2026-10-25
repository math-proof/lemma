import Mathlib
import Lemma.ModularCurve.QAdicPlace
import Lemma.ModularCurve.JqCoeff
import Lemma.ModularCurve.QAdicPlaceMod

noncomputable section InlinedTheorems

namespace ModularCurve
namespace CharLRows

open HahnSeries

variable (K : Type*) [CommRing K]

private theorem jqModC_pow (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

private theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

private theorem coeff_jqModC_pow_self (n : ℕ) : ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

private theorem coeff_jqModC_pow_of_lt_loc {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : ((jqModC K) ^ n).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

private theorem coeff_jqModC_neg_one_loc : (jqModC K).coeff (-1 : ℤ) = 1 := by
  simpa using coeff_jqModC_pow_self K 1

end CharLRows
end ModularCurve

open ModularCurve in

private theorem ModularCurve.coeff_jqModC_neg_one_loc (K : Type*) [CommRing K] :
    (jqModC K).coeff (-1 : ℤ) = 1 :=
  CharLRows.coeff_jqModC_neg_one_loc K

open ModularCurve in

private theorem ModularCurve.coeff_jqModC_pow_of_lt_loc (K : Type*) [CommRing K] {b : ℕ} {m : ℤ} (hm : m < -(b : ℤ)) :
    ((jqModC K) ^ b).coeff m = 0 :=
  CharLRows.coeff_jqModC_pow_of_lt_loc K hm

end InlinedTheorems

set_option autoImplicit false

noncomputable section

open HahnSeries AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000

namespace ModularCurve

variable (K : Type*) [Field K]

section OrderJqModC

end OrderJqModC

section QAdicPlaceMod


end QAdicPlaceMod

section LevelN


end LevelN

section Gates

end Gates

end ModularCurve
