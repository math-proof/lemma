import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial
open scoped Polynomial.Bivariate


private lemma eval₂_reflect_inv {R K : Type*} [CommRing R] [Field K] (f : R →+* K) {x : K} (hx : x ≠ 0)
  (D : ℕ) (a : R[X]) (ha : a.natDegree ≤ D) :
  eval₂ f x⁻¹ (reflect D a) = eval₂ f x a * x⁻¹ ^ D := by
  let : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := eval₂_reflect_mul_pow f x⁻¹ D a ha
  rw [invOf_eq_inv, inv_inv] at h
  let : Invertible x := invertibleOfNonzero hx
  have h' := eval₂_reflect_mul_pow f x D a ha
  rw [invOf_eq_inv] at h'
  calc
    _ = eval₂ f x⁻¹ (reflect D a) * x ^ D * x⁻¹ ^ D := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, mul_one]
    _ = eval₂ f x a * x⁻¹ ^ D := by rw [h']

private lemma exists_monic_eval₂_inv_mul_inv_pow_eq_zero {R K : Type*} [CommRing R] [Nontrivial R]
  [Field K] (f : R →+* K) (P : R[X][Y]) (hP : P.Monic) (m : ℕ)
  (hdeg : ∀ i < P.natDegree, (P.coeff i).natDegree ≤ m * (P.natDegree - i))
  {x : K} (hx : x ≠ 0) (y : K) (hroot : P.eval₂ (eval₂RingHom f x) y = 0) :
  ∃ Q : R[X][Y], Q.Monic ∧ Q.natDegree = P.natDegree ∧
    Q.eval₂ (eval₂RingHom f x⁻¹) (y * x⁻¹ ^ m) = 0 := by
  set n := P.natDegree with hn
  let c : ℕ → R[X] := fun i ↦ reflect (m * (n - i)) (P.coeff i)
  let Q : R[X][Y] := Y ^ n + ∑ i : Fin n, C (c i) * Y ^ (i : ℕ)
  have hQmonic : Q.Monic := by
    refine (monic_X_pow n).add_of_left ?_
    rw [degree_X_pow]
    exact degree_sum_fin_lt _
  have hQdeg : Q.natDegree = n := by
    have h1 : (Y ^ n + ∑ i : Fin n, C (c i) * Y ^ (i : ℕ) : R[X][Y]).natDegree =
      (Y ^ n : R[X][Y]).natDegree :=
      natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _)
    rw [h1, natDegree_X_pow]
  refine ⟨Q, hQmonic, hQdeg, ?_⟩
  set φ : R[X] →+* K := eval₂RingHom f x with hφ
  set φ' : R[X] →+* K := eval₂RingHom f x⁻¹ with hφ'
  set z : K := y * x⁻¹ ^ m with hz
  have hcn : c n = 1 := by
    simp only [c, Nat.sub_self, mul_zero]
    rw [show P.coeff n = 1 from hP.coeff_natDegree, ← C_1, reflect_C, pow_zero, mul_one]
  have hterm : ∀ i ≤ n, φ' (c i) * z ^ i = x⁻¹ ^ (m * n) * (φ (P.coeff i) * y ^ i) := by
    intro i hi
    have hdi : (P.coeff i).natDegree ≤ m * (n - i) := by
      obtain hlt | rfl := lt_or_eq_of_le hi
      · exact hdeg i hlt
      ·
        rw [show P.coeff n = 1 from hP.coeff_natDegree, natDegree_one]
        exact Nat.zero_le _
    have h1 : φ' (c i) = φ (P.coeff i) * x⁻¹ ^ (m * (n - i)) := by
      simp only [hφ', hφ, coe_eval₂RingHom, c]
      exact eval₂_reflect_inv f hx _ _ hdi
    rw [h1, hz, mul_pow, ← pow_mul]
    have hexp : m * (n - i) + m * i = m * n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hi]
    calc
      _ = φ (P.coeff i) * y ^ i * (x⁻¹ ^ (m * (n - i)) * x⁻¹ ^ (m * i)) := by ring
      _ = φ (P.coeff i) * y ^ i * x⁻¹ ^ (m * n) := by rw [← pow_add, hexp]
      _ = x⁻¹ ^ (m * n) * (φ (P.coeff i) * y ^ i) := by ring
  have hevalQ : Q.eval₂ φ' z = ∑ i ∈ Finset.range (n + 1), φ' (c i) * z ^ i := by
    simp only [Q, eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C]
    rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range (fun i ↦ φ' (c i) * z ^ i) n, hcn,
      map_one, one_mul, add_comm]
  have hevalP : P.eval₂ φ y = ∑ i ∈ Finset.range (n + 1), φ (P.coeff i) * y ^ i :=
    eval₂_eq_sum_range φ y
  rw [hevalQ]
  calc
    _ = ∑ i ∈ Finset.range (n + 1), x⁻¹ ^ (m * n) * (φ (P.coeff i) * y ^ i) := by
      refine Finset.sum_congr rfl fun i hi ↦ hterm i ?_
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    _ = x⁻¹ ^ (m * n) * P.eval₂ φ y := by rw [hevalP, Finset.mul_sum]
    _ = 0 := by rw [hroot, mul_zero]
/--
[ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero.lean)
-/
@[path]
private lemma main
  [CommRing R] [Nontrivial R] [Field K]
  {f : R →+* K}
  {P : R[X][Y]}
  {m : ℕ}
  {x : K}
  {y : K}
-- given
  (hP : P.Monic)
  (hdeg : ∀ i < P.natDegree, (P.coeff i).natDegree ≤ m * (P.natDegree - i))
  (hx : x ≠ 0)
  (hroot : P.eval₂ (eval₂RingHom f x) y = 0) :
-- imply
  ∃ Q : R[X][Y], Q.Monic ∧ Q.natDegree = P.natDegree ∧
      Q.eval₂ (eval₂RingHom f x⁻¹) (y * x⁻¹ ^ m) = 0 :=
-- proof
  exists_monic_eval₂_inv_mul_inv_pow_eq_zero f P hP m hdeg hx y hroot


-- created on 2026-10-23
