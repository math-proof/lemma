import Mathlib
import sympy.Basic

open MvPolynomial

/--
[MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean)
-/

private lemma  isHomogeneous_iterate_pderiv {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ} (k : σ)
    (hφ : φ.IsHomogeneous n) (j : ℕ) : ((pderiv k)^[j] φ).IsHomogeneous (n - j) := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa [Nat.sub_sub] using ih.pderiv

private lemma  iterate_pderiv_eq_zero_of_lt {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) : (pderiv k)^[i] φ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [show n + m + 1 = m + 1 + n by ring, Function.iterate_add_apply, Function.iterate_succ_apply]
  have h0 : ((pderiv k)^[n] φ).IsHomogeneous 0 := by
    simpa using isHomogeneous_iterate_pderiv k hφ n
  have hC : (pderiv k)^[n] φ = C (coeff 0 ((pderiv k)^[n] φ)) :=
    totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h0.totalDegree_le)
  rw [hC, pderiv_C]
  exact Function.iterate_fixed (map_zero _) m
@[main]
private lemma main
  {σ R : Type*} [CommSemiring R]
  {φ : MvPolynomial σ R}
  {n : ℕ}
  {k : σ}
  {i : ℕ}
-- given
  (hφ : φ.IsHomogeneous n)
  (hi : n < i) :
-- imply
  (MvPolynomial.pderiv k)^[i] φ = 0 :=
-- proof
  iterate_pderiv_eq_zero_of_lt hφ k hi


-- created on 2026-10-05
