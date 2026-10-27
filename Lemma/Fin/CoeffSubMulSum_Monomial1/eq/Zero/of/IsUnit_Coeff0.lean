import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


private lemma sum_fin_monomial_eq_trunc
  {A : Type*}
  [CommRing A]
  (m : ℕ) (φ : PowerSeries A) :
  (∑ r' : Fin (m + 1), monomial (r' : ℕ) (PowerSeries.coeff (r' : ℕ) φ)) = PowerSeries.trunc (m + 1) φ := by
  ext k
  rw [finsetSum_coeff, PowerSeries.coeff_trunc,
    ← Finset.sum_range (fun i => (monomial i (PowerSeries.coeff i φ)).coeff k)]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]

private lemma exists_inv_jet
  {A : Type*}
  [CommRing A]
  (s : Polynomial A) (hs : IsUnit (s.coeff 0)) (m : ℕ) :
  ∃ σ : Fin (m + 1) → A,
    ∀ r : Fin (m + 1), ((∑ r' : Fin (m + 1), monomial (r' : ℕ) (σ r')) * s - 1).coeff r = 0 := by
  obtain ⟨u, hu⟩ := hs
  set I : PowerSeries A := PowerSeries.invOfUnit (s : PowerSeries A) u with hI
  have hinv : (s : PowerSeries A) * I = 1 :=
    PowerSeries.mul_invOfUnit (s : PowerSeries A) u
      (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hu])
  refine ⟨fun r' => PowerSeries.coeff (r' : ℕ) I, fun r => ?_⟩
  have key : (PowerSeries.trunc (m + 1) I * s).coeff (r : ℕ) = (1 : A[X]).coeff (r : ℕ) := by
    have h1 : PowerSeries.trunc (m + 1) ((PowerSeries.trunc (m + 1) I : PowerSeries A) * (s : PowerSeries A)) = 1 := by
      rw [PowerSeries.trunc_trunc_mul, mul_comm, hinv, PowerSeries.trunc_one]
    have h2 : (PowerSeries.trunc (m + 1)
      ((PowerSeries.trunc (m + 1) I : PowerSeries A) * (s : PowerSeries A))).coeff (r : ℕ) = (1 : A[X]).coeff (r : ℕ) := by
      rw [h1]
    rwa [PowerSeries.coeff_trunc, if_pos r.2, ← Polynomial.coe_mul, Polynomial.coeff_coe] at h2
  rw [sum_fin_monomial_eq_trunc, coeff_sub, key, sub_self]
/--
[Polynomial_exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_exists_coeff_sum_monomial_mul_sub_one_eq_zero_of_isUnit_coeff_zero.lean)
-/
@[path]
private lemma main
  [CommRing A]
  {s : Polynomial A}
  {m : ℕ}
-- given
  (hs : IsUnit (s.coeff 0)) :
-- imply
  ∃ σ : Fin (m + 1) → A,
      ∀ r : Fin (m + 1), ((∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (σ r')) * s - 1).coeff r = 0 :=
-- proof
  exists_inv_jet s hs m


-- created on 2026-10-23
