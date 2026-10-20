/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Polynomial/ZeilbergerGamma.lean -/

import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Zeilberger's lemma for the gamma expansion of Pascal-like triangles.
-/

section

namespace MetaMathlibExt

open scoped BigOperators

/-- Zeilberger's lemma: extraction of `gamma k` from `h_n (x * c(x)^2) / c(x)^n`,
where `c` is the Catalan generating function.

Provenance: Paul Barry, "The γ-Vectors of Pascal-like Triangles Defined by
Riordan Arrays", Journal of Integer Sequences 22 (2019), Article 19.1.4,
Zeilberger's Lemma proposition lines 281–283,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Barry2/barry402.tex>.
The gamma-matrix setup and `h` notation use supporting lines 110–120; the
Catalan generating function `c(x) = (1 - sqrt (1 - 4 * x)) / (2 * x)` has
coefficients `C_n = (1 / (n + 1)) * choose (2 * n) n` (A000108).
The malformed recalled display at source line 275 printing `gamma_n` on both
sides is excluded; the correctly printed proposition with `h_n` on the left
is formalized.

Proves `Wanted` entry `zeilberger_gamma_coefficient`.
-/
theorem zeilberger_gamma_coefficient
    (n k : ℕ) (h : Polynomial ℚ) (gamma : ℕ → ℚ)
    (hk : k ≤ n / 2)
    (hgamma :
      h = ∑ j ∈ Finset.range (n / 2 + 1),
        Polynomial.C (gamma j) * Polynomial.X ^ j *
          (1 + Polynomial.X) ^ (n - 2 * j)) :
    let C : PowerSeries ℚ :=
      PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries
    gamma k =
      PowerSeries.coeff k
        ((Polynomial.aeval (PowerSeries.X * C ^ 2) h) * (C ^ n)⁻¹) := by
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
    rw [map_pow, hC0, one_pow]
    exact one_ne_zero
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

end
