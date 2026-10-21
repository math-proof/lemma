import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv.lean)
-/
@[path]
private lemma main
  [Field L] [Field F] [Algebra L F]
  (x : F)
  (c : Polynomial L)
  (n : ℕ)
  -- given
  (hxL : Transcendental L x)
  (hx0 : x ≠ 0)
  (h : Polynomial.aeval x c * (x ^ n)⁻¹ ∈ Algebra.adjoin L ({x⁻¹} : Set F)) :
  -- imply
  c.natDegree ≤ n := by
  -- proof
  classical
  if hc0 : c = 0 then
    simp [hc0]
  else
    rw [Algebra.adjoin_singleton_eq_range_aeval L x⁻¹, AlgHom.mem_range] at h
    obtain ⟨p, hp⟩ := h
    set N : ℕ := max n p.natDegree with hN
    have hnN : n ≤ N := le_max_left _ _
    have hpN : p.natDegree ≤ N := le_max_right _ _
    let _ : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx0)
    have hxinvinv : ⅟(x⁻¹) = x := by
      rw [invOf_eq_inv, inv_inv]
    have hrefl : Polynomial.aeval x (p.reflect N) * (x⁻¹) ^ N = Polynomial.aeval x⁻¹ p := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def]
      have := Polynomial.eval₂_reflect_mul_pow (algebraMap L F) x⁻¹ N p hpN
      rwa [hxinvinv] at this
    have heq : Polynomial.aeval x (p.reflect N) = Polynomial.aeval x (c * Polynomial.X ^ (N - n)) := by
      have hxN0 : (x ^ N : F) ≠ 0 := pow_ne_zero N hx0
      have h1 : Polynomial.aeval x (p.reflect N) * (x⁻¹) ^ N * x ^ N =
          Polynomial.aeval x c * (x ^ n)⁻¹ * x ^ N := by
        rw [hrefl, hp]
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hx0, one_pow, mul_one] at h1
      rw [h1, map_mul, Polynomial.aeval_X_pow, mul_assoc, mul_comm ((x ^ n)⁻¹) (x ^ N), ← pow_sub₀ x hx0 hnN]
    have hpoly : p.reflect N = c * Polynomial.X ^ (N - n) := (transcendental_iff_injective.mp hxL) heq
    have hdeg : c.natDegree + (N - n) ≤ N := calc
      _ = (c * Polynomial.X ^ (N - n)).natDegree := by
        rw [Polynomial.natDegree_mul hc0 (pow_ne_zero _ Polynomial.X_ne_zero), Polynomial.natDegree_X_pow]
      _ = (p.reflect N).natDegree := by
        rw [hpoly]
      _ ≤ max N p.natDegree := Polynomial.natDegree_reflect_le
      _ = N := max_eq_left hpN
    omega


-- created on 2026-10-20
