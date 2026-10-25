import Mathlib
import sympy.Basic
import Lemma.ModularCurve.EtaQuotient
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_isMonicOfOrder_sharpUnitSeries](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_isMonicOfOrder_sharpUnitSeries.lean)
-/

private lemma isMonic_sharp (ℓ : ℕ) [NeZero ℓ] :
  IsMonicOfOrder (sharpUnitSeries ℓ) (-(eisensteinNumerator ℓ : ℤ)) := by
  set P : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ) with hP
  have hPm : IsMonicOfOrder P 0 := IsMonicOfOrder.ofPowerSeries (constantCoeff_etaProdPow ℓ)
  have hQm : IsMonicOfOrder (qExpand ℚ ℓ P) 0 := by
    have h := hPm.qExpand ℓ
    rwa [mul_zero] at h
  have hQne : qExpand ℚ ℓ P ≠ 0 := hQm.ne_zero
  have hfg : IsMonicOfOrder (sharpUnitSeries ℓ * qExpand ℚ ℓ P)
    (-(eisensteinNumerator ℓ : ℤ)) := by
    have hcancel : sharpUnitSeries ℓ * qExpand ℚ ℓ P = HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) * P := by
      rw [sharpUnitSeries_def, ← hP, mul_assoc, inv_mul_cancel₀ hQne, mul_one]
    rw [hcancel]
    have h := (IsMonicOfOrder.single (-(eisensteinNumerator ℓ : ℤ))).mul hPm
    rwa [add_zero] at h
  have h := hfg.of_mul_right hQm
  rwa [sub_zero] at h
@[path]
private lemma main
  {ℓ : ℕ} [NeZero ℓ] :
-- imply
  ModularCurve.IsMonicOfOrder (ModularCurve.sharpUnitSeries ℓ) (-(ModularCurve.eisensteinNumerator ℓ : ℤ)) :=
-- proof
  isMonic_sharp ℓ


-- created on 2026-10-23
