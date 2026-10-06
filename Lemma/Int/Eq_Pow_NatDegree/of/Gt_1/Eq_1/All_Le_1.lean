import Mathlib
import sympy.Basic


/--
[Valuation_map_eval_eq_pow_of_one_lt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Valuation_map_eval_eq_pow_of_one_lt.lean)
-/
@[main]
private lemma main
  [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation R Γ₀}
  {f : Polynomial R}
  {x : R}
-- given
  (hc : ∀ i, v (f.coeff i) ≤ 1)
  (hl : v f.leadingCoeff = 1)
  (hx : 1 < v x) :
-- imply
  v (f.eval x) = v x ^ f.natDegree := by
-- proof
  have hx0 : v x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl' : v (f.coeff f.natDegree) = 1 := hl
  have htop : v (f.coeff f.natDegree * x ^ f.natDegree) = v x ^ f.natDegree := by
    rw [map_mul, map_pow, hl', one_mul]
  have hlower : v (∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i)
      < v x ^ f.natDegree := by
    refine v.map_sum_lt (pow_ne_zero _ hx0) ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc v (f.coeff i) * v x ^ i ≤ 1 * v x ^ i := mul_le_mul' (hc i) le_rfl
      _ = v x ^ i := one_mul _
      _ < v x ^ f.natDegree := pow_lt_pow_right₀ hx hi
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ,
    Valuation.map_add_eq_of_lt_right _ (htop ▸ hlower), htop]


-- created on 2026-10-05
