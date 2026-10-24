import Mathlib
import sympy.Basic
open HahnSeries Polynomial
open LaurentSeries


private lemma algebraMap_eq_C
  {K : Type u}
  [Field K]
  (c : K) : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C]

private lemma coeff_C_mul'
  {K : Type u}
  [Field K]
  (c : K) (y : LaurentSeries K) (a : ℤ) : (HahnSeries.C c * y).coeff a = c * y.coeff a :=
  HahnSeries.coeff_single_zero_mul

private lemma order_eq_zero_of_isAlgebraic
  {K : Type u}
  [Field K]
  (x : LaurentSeries K) (hx : IsAlgebraic K x) (h0 : x ≠ 0) :
  x.order = 0 := by
  classical
  by_contra hn
  obtain ⟨p, hp0, hpx⟩ := hx
  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  obtain ⟨i₀, hi₀, hmin⟩ := p.support.exists_min_image (fun i : ℕ => (i : ℤ) * x.order) hsupp
  have hstrict : ∀ i ∈ p.support, i ≠ i₀ → (i₀ : ℤ) * x.order < (i : ℤ) * x.order := by
    intro i hi hne
    refine lt_of_le_of_ne (hmin i hi) ?_
    intro heq
    apply hne
    have := mul_right_cancel₀ hn heq
    exact_mod_cast this.symm
  have hpx' : (∑ i ∈ p.support, HahnSeries.C (p.coeff i) * x ^ i) = 0 := by
    rw [← hpx, aeval_def, eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebraMap_eq_C]
  have hrel := congrArg (fun y : LaurentSeries K => y.coeff ((i₀ : ℤ) * x.order)) hpx'
  simp only [HahnSeries.coeff_zero] at hrel
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single i₀] at hrel
  ·
    have hx0 : x ^ i₀ ≠ 0 := pow_ne_zero _ h0
    have hord : (x ^ i₀).order = (i₀ : ℤ) * x.order := by
      rw [HahnSeries.order_pow, nsmul_eq_mul]
    rw [coeff_C_mul', ← hord] at hrel
    exact (mul_ne_zero (Polynomial.mem_support_iff.mp hi₀) (mt HahnSeries.coeff_order_eq_zero.mp hx0)) hrel
  ·
    intro i hi hne
    rw [coeff_C_mul', HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
    rw [HahnSeries.order_pow, nsmul_eq_mul]
    exact hstrict i hi hne
  ·
    intro h
    exact absurd hi₀ h

private lemma exists_eq_C_of_isAlgebraic
  {K : Type u}
  [Field K]
  (x : LaurentSeries K) (hx : IsAlgebraic K x) :
  ∃ c : K, x = HahnSeries.C c := by
  refine ⟨x.coeff 0, ?_⟩
  have hCa : ∀ c : K, (algebraMap K (LaurentSeries K) c) = HahnSeries.C c := algebraMap_eq_C
  set y : LaurentSeries K := x - algebraMap K (LaurentSeries K) (x.coeff 0) with hy
  have hyalg : IsAlgebraic K y :=
    hx.sub (isAlgebraic_algebraMap (R := K) (A := LaurentSeries K) (x.coeff 0))
  if hy0 : y = 0 then
    rw [hy, sub_eq_zero] at hy0
    rwa [← hCa]
  else
    exfalso
    have hord := order_eq_zero_of_isAlgebraic y hyalg hy0
    have hcoeff : y.coeff 0 = 0 := by
      rw [hy, HahnSeries.coeff_sub, hCa, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_self]
    have := mt HahnSeries.coeff_order_eq_zero.mp hy0
    rw [hord, hcoeff] at this
    exact this rfl
/--
[LaurentSeries_exists_eq_C_of_isAlgebraic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LaurentSeries_exists_eq_C_of_isAlgebraic.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {x : LaurentSeries K}
-- given
  (hx : IsAlgebraic K x) :
-- imply
  ∃ c : K, x = HahnSeries.C c :=
-- proof
  exists_eq_C_of_isAlgebraic x hx


-- created on 2026-10-23
