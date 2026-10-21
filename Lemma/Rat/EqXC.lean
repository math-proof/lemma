import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma algebraMap_eq_C
  [Field K]
  (c : K) :
  -- imply
  algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  -- proof
  rw [HahnSeries.algebraMap_apply']
  simp

private lemma order_nonneg_of_isAlgebraic
  [Field K]
  {x : LaurentSeries K}
  -- given
  (hx : IsAlgebraic K x)
  (hx0 : x ≠ 0) :
  -- imply
  0 ≤ x.order := by
  -- proof
  by_contra hneg
  push Not at hneg
  obtain ⟨p, hp0, hpx⟩ := hx
  set d := p.natDegree with hd
  have hne : (x ^ d).coeff (d • x.order) ≠ 0 := by
    rw [← HahnSeries.order_pow x d]
    apply (HahnSeries.coeff_order_eq_zero.not.mpr (pow_ne_zero d hx0))
  have key : (Polynomial.aeval x p).coeff (d • x.order) = p.coeff d * (x ^ d).coeff (d • x.order) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    simp only [HahnSeries.coeff_sum, algebraMap_eq_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    intro i hi
    rw [Finset.mem_range] at hi
    if hpi : p.coeff i = 0 then
      rw [hpi, zero_mul]
    else
      have hlt : d • x.order < (x ^ i).order := by
        rw [HahnSeries.order_pow, nsmul_eq_mul, nsmul_eq_mul]
        have hi' : (i : ℤ) < (d : ℤ) := by
          exact_mod_cast hi
        nlinarith
      rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, mul_zero]
  have hlead : p.coeff d ≠ 0 := by
    rw [hd]
    apply Polynomial.leadingCoeff_ne_zero.mpr hp0
  have h : (Polynomial.aeval x p).coeff (d • x.order) ≠ 0 := by
    rw [key]
    apply mul_ne_zero hlead hne
  refine h ?_
  rw [hpx]
  rfl

private lemma order_eq_zero_of_isAlgebraic
  [Field K]
  {x : LaurentSeries K}
  -- given
  (hx : IsAlgebraic K x)
  (hx0 : x ≠ 0) :
  -- imply
  x.order = 0 := by
  -- proof
  have h1 := order_nonneg_of_isAlgebraic hx hx0
  have h2 := order_nonneg_of_isAlgebraic hx.inv (inv_ne_zero hx0)
  have h3 : x.order + x⁻¹.order = 0 := by
    rw [← HahnSeries.order_mul hx0 (inv_ne_zero hx0), mul_inv_cancel₀ hx0, HahnSeries.order_one]
  omega

/--
[LaurentSeries_eq_C_coeff_zero_of_isAlgebraic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic.lean)
-/
@[path]
private lemma main
  [Field K]
  {x : LaurentSeries K}
  -- given
  (hx : IsAlgebraic K x) :
  -- imply
  x = HahnSeries.C (x.coeff 0) := by
  -- proof
  set y : LaurentSeries K := x - HahnSeries.C (x.coeff 0) with hy
  have hyalg : IsAlgebraic K y := by
    refine hx.sub ?_
    rw [← algebraMap_eq_C]
    apply isAlgebraic_algebraMap _
  if hy0 : y = 0 then
    apply sub_eq_zero.mp hy0
  else
    exfalso
    have hord := order_eq_zero_of_isAlgebraic hyalg hy0
    have hc : y.coeff y.order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hy0
    rw [hord] at hc
    apply hc
    simp [hy]


-- created on 2026-10-20
