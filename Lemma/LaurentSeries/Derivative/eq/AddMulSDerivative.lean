import Mathlib
import sympy.Basic
open HahnSeries
open LaurentSeries


noncomputable def thetaR
  {R : Type*}
  [CommRing R]
  (f : LaurentSeries R) : LaurentSeries R :=
  single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f

private lemma coeff_single_one_mul_derivative_add_one
  {R : Type*}
  [CommRing R]
  (f : LaurentSeries R) (m : ℤ) :
  (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff (m + 1) =
    ((m + 1 : ℤ) : R) * f.coeff (m + 1) := by
  rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  simp only [Nat.cast_one]

private lemma coeff_single_one_mul_derivative
  {R : Type*}
  [CommRing R]
  (f : LaurentSeries R) (n : ℤ) :
  (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff n = (n : R) * f.coeff n := by
  have h := coeff_single_one_mul_derivative_add_one f (n - 1)
  simp only [sub_add_cancel] at h
  exact h

private lemma coeff_thetaR
  {R : Type*}
  [CommRing R]
  (f : LaurentSeries R) (n : ℤ) : (thetaR f).coeff n = (n : R) * f.coeff n :=
  coeff_single_one_mul_derivative f n

private lemma thetaR_add
  {R : Type*}
  [CommRing R]
  (f g : LaurentSeries R) : thetaR (f + g) = thetaR f + thetaR g := by
  ext n; simp [coeff_thetaR, mul_add]

private lemma thetaR_sub
  {R : Type*}
  [CommRing R]
  (f g : LaurentSeries R) : thetaR (f - g) = thetaR f - thetaR g := by
  ext n; simp [coeff_thetaR, mul_sub]

private lemma thetaR_natCast_mul
  {R : Type*}
  [CommRing R]
  (m : ℕ) (f : LaurentSeries R) :
  thetaR ((m : LaurentSeries R) * f) = (m : LaurentSeries R) * thetaR f := by
  ext n
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) m, HahnSeries.C_mul_eq_smul,
    HahnSeries.C_mul_eq_smul, coeff_thetaR, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
    coeff_thetaR, smul_eq_mul, smul_eq_mul]
  ring

private lemma support_thetaR_subset
  {R : Type*}
  [CommRing R]
  (f : LaurentSeries R) : (thetaR f).support ⊆ f.support := by
  intro n hn
  rw [HahnSeries.mem_support, coeff_thetaR] at hn
  rw [HahnSeries.mem_support]
  exact right_ne_zero_of_mul hn

private lemma thetaR_mul
  {R : Type*}
  [CommRing R]
  (f g : LaurentSeries R) : thetaR (f * g) = thetaR f * g + f * thetaR g := by
  ext n
  rw [HahnSeries.coeff_add, coeff_thetaR, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_left' f.isPWO_support (support_thetaR_subset f),
    HahnSeries.coeff_mul_right' g.isPWO_support (support_thetaR_subset g),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  rw [coeff_thetaR, coeff_thetaR, ← hsum, Int.cast_add]
  ring

private lemma single_one_mul_injective
  {R : Type*}
  [CommRing R]
  : Function.Injective fun x : LaurentSeries R => single (1 : ℤ) (1 : R) * x := by
  intro x y h
  ext n
  have h' := congrArg (fun w : LaurentSeries R => w.coeff (n + 1)) h
  simpa [HahnSeries.coeff_single_mul_add] using h'

private lemma helper_main
  {R : Type*}
  [CommRing R]
  (f g : LaurentSeries R) :
  LaurentSeries.derivative R (f * g) =
    LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g := by
  apply single_one_mul_injective
  show single (1 : ℤ) (1 : R) * LaurentSeries.derivative R (f * g) =
    single (1 : ℤ) (1 : R) * (LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g)
  have h := thetaR_mul f g
  simp only [thetaR] at h
  rw [h]; ring
/--
[LaurentSeries_derivative_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LaurentSeries_derivative_mul.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {f g : LaurentSeries R} :
-- imply
  LaurentSeries.derivative R (f * g) =
      LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g :=
-- proof
  helper_main f g


-- created on 2026-10-23
