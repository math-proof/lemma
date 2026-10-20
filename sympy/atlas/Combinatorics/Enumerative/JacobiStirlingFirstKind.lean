/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Coeff

open scoped BigOperators

namespace MetaMathlibExt

/-- N-th first-kind Jacobi-Stirling generating polynomial over a commutative ring,
the product over `i < n` of `X - C (i * (i + ζ))`.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, source equation `e:JacobiStirling1`. -/
noncomputable def jacobiStirlingFirstPoly {R : Type*} [CommRing R]
    (n : ℕ) (ζ : R) : Polynomial R :=
  ∏ i ∈ Finset.range n,
    (Polynomial.X - Polynomial.C ((i : R) * ((i : R) + ζ)))

/-- First-kind Jacobi-Stirling numbers `J(n,k;ζ)`, defined as the coefficient
of `X^k` in the generating polynomial.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, source equation `e:JacobiStirling1`. -/
noncomputable def jacobiStirlingFirst {R : Type*} [CommRing R]
    (n k : ℕ) (ζ : R) : R :=
  (jacobiStirlingFirstPoly n ζ).coeff k

/-- Initial row: `J(0,k;ζ)` is `1` when `k = 0` and `0` otherwise.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1` note `J(0,k;ζ) = δ_{0,k}`. -/
theorem jacobiStirlingFirst_initial_row {R : Type*} [CommRing R]
    (k : ℕ) (ζ : R) :
    jacobiStirlingFirst 0 k ζ = if k = 0 then 1 else 0 := by
  unfold jacobiStirlingFirst jacobiStirlingFirstPoly
  simp [Polynomial.coeff_one]

/-- Triangular recurrence:
`J(n+1,k+1;ζ) = J(n,k;ζ) - n * (n + ζ) * J(n,k+1;ζ)`.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1` with factor
`X - n * (n + ζ)`. -/
theorem jacobiStirlingFirst_recurrence {R : Type*} [CommRing R]
    (n k : ℕ) (ζ : R) :
    jacobiStirlingFirst (n + 1) (k + 1) ζ =
      jacobiStirlingFirst n k ζ -
        (n : R) * ((n : R) + ζ) * jacobiStirlingFirst n (k + 1) ζ := by
  unfold jacobiStirlingFirst
  have hprod : jacobiStirlingFirstPoly (n + 1) ζ =
      jacobiStirlingFirstPoly n ζ *
        (Polynomial.X - Polynomial.C ((n : R) * ((n : R) + ζ))) := by
    unfold jacobiStirlingFirstPoly
    rw [Finset.prod_range_succ]
  rw [hprod, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
    Polynomial.coeff_mul_C,
    mul_comm ((jacobiStirlingFirstPoly n ζ).coeff (k + 1)) _]

/-- Support: `J(n,k;ζ) = 0` for `k > n`.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1`. -/
theorem jacobiStirlingFirst_support {R : Type*} [CommRing R]
    (n k : ℕ) (ζ : R) (h : n < k) :
    jacobiStirlingFirst n k ζ = 0 := by
  induction n generalizing k with
  | zero =>
    have hk : k ≠ 0 := by omega
    have h0 := jacobiStirlingFirst_initial_row k ζ
    rw [ite_eq_right hk] at h0
    exact h0
  | succ n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have h1 : n < m := by omega
    have h2 : n < m + 1 := by omega
    have e1 : jacobiStirlingFirst n m ζ = 0 := ih m h1
    have e2 : jacobiStirlingFirst n (m + 1) ζ = 0 := ih (m + 1) h2
    rw [jacobiStirlingFirst_recurrence, e1, e2, mul_zero, sub_self]

/-- Diagonal: `J(n,n;ζ) = 1`.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1`. -/
theorem jacobiStirlingFirst_diagonal {R : Type*} [CommRing R]
    (n : ℕ) (ζ : R) :
    jacobiStirlingFirst n n ζ = 1 := by
  induction n with
  | zero =>
    have h0 := jacobiStirlingFirst_initial_row 0 ζ
    rw [ite_eq_left rfl] at h0
    exact h0
  | succ n ih =>
    rw [jacobiStirlingFirst_recurrence, ih,
      jacobiStirlingFirst_support n (n + 1) ζ (by omega), mul_zero, sub_zero]

end MetaMathlibExt
