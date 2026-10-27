import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped BigOperators


namespace MetaMathlibExt

/--
[zeilberger_gamma_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Polynomial/ZeilbergerGamma.lean)
-/
@[path]
lemma zeilberger_gamma_coefficient
  {n k : ℕ}
  {gamma : ℕ → ℚ}
-- given
  (h : Polynomial ℚ)
  (hk : k ≤ n / 2)
  (hgamma : h = ∑ j ∈ Finset.range (n / 2 + 1), Polynomial.C (gamma j) * Polynomial.X ^ j * (1 + Polynomial.X) ^ (n - 2 * j)) :
-- imply
  let C : PowerSeries ℚ := by
-- proof
  intro C
  -- Catalan relation mapped to ℚ
  have hcat : C ^ 2 * PowerSeries.X + 1 = C := by
    have h := PowerSeries.catalanSeries_sq_mul_X_add_one
    have h2 := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) h
    simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h2
    simpa using h2
  have hC0 : PowerSeries.constantCoeff C = 1 := by
    have hcc : PowerSeries.constantCoeff C =
      (Nat.castRingHom ℚ) (PowerSeries.constantCoeff PowerSeries.catalanSeries) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    rw [hcc, PowerSeries.catalanSeries_constantCoeff, map_one]
  have hCn0 : PowerSeries.constantCoeff (C ^ n) ≠ 0 := by
    rwa [map_pow, hC0, one_pow]
  have h1 : 1 + PowerSeries.X * C ^ 2 = C := by
    linear_combination hcat
  have hCinv : C ^ n * (C ^ n)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hCn0
  -- evaluation identity
  have haeval : Polynomial.aeval (PowerSeries.X * C ^ 2) h =
    (∑ j ∈ Finset.range (n / 2 + 1),
      PowerSeries.C (gamma j) * PowerSeries.X ^ j) * C ^ n := by
    rw [hgamma, map_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hj2 : 2 * j ≤ n := by
      have hmem : j < n / 2 + 1 := Finset.mem_range.mp hj
      omega
    have hy : (PowerSeries.X * C ^ 2) ^ j * C ^ (n - 2 * j)
      = PowerSeries.X ^ j * C ^ n := by
      rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, Nat.add_sub_cancel' hj2]
    have step : (Polynomial.aeval (PowerSeries.X * C ^ 2))
      (Polynomial.C (gamma j) * Polynomial.X ^ j * (1 + Polynomial.X) ^ (n - 2 * j))
      = PowerSeries.C (gamma j) * ((PowerSeries.X * C ^ 2) ^ j * C ^ (n - 2 * j)) := by
      simp only [map_mul, map_pow, map_add, map_one, Polynomial.aeval_X,
        Polynomial.aeval_C, PowerSeries.algebraMap_eq, h1]
      ring
    rw [step, hy]
    ring
  -- extract coefficient
  have hcoeff : PowerSeries.coeff k
    ((∑ j ∈ Finset.range (n / 2 + 1),
      PowerSeries.C (gamma j) * PowerSeries.X ^ j)) = gamma k := by
    rw [map_sum]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    have hkmem : k ∈ Finset.range (n / 2 + 1) := Finset.mem_range.mpr (by omega)
    have : (∑ j ∈ Finset.range (n / 2 + 1), (if k = j then gamma j else 0)) = gamma k := by
      simp only [eq_comm (a := k)] at *
      rw [Finset.sum_ite_eq' _ k (fun j => gamma j)]
      simp [hkmem]
    exact this
  calc gamma k = PowerSeries.coeff k
    ((∑ j ∈ Finset.range (n / 2 + 1),
      PowerSeries.C (gamma j) * PowerSeries.X ^ j)) := hcoeff.symm
    _ = PowerSeries.coeff k
      (((∑ j ∈ Finset.range (n / 2 + 1),
        PowerSeries.C (gamma j) * PowerSeries.X ^ j) * C ^ n) * (C ^ n)⁻¹) := by
      rw [mul_assoc, hCinv, mul_one]
    _ = PowerSeries.coeff k
      ((Polynomial.aeval (PowerSeries.X * C ^ 2) h) * (C ^ n)⁻¹) := by
      rw [haeval]
end MetaMathlibExt



-- created on 2026-10-20
-- updated on 2026-10-26
