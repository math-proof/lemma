import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Enumerative.EulerianPolynomialHankel.Part2
open MetaMathlibExt


namespace MetaMathlibExt

/--
[ehd_poly_coeff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_poly_coeff_eq (m k : ℕ) :
  (ehd_poly m).coeff k = if k < m + 1 then ehd_coeff m k else 0 := by
  rw [ehd_poly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  simp [eq_comm, Finset.mem_range, Finset.sum_ite_eq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_altSum_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_altSum_succ (m q : ℕ) (hq : q ≤ m + 1) :
  ehd_altSum (m + 1) (q + 1) =
    (q + 1 : ℤ) * ehd_altSum m (q + 1) +
      (m + 1 - q : ℕ) * ehd_altSum m q := by
  unfold ehd_altSum
  rw [Finset.sum_range_succ'
    (fun i => (-1 : ℤ) ^ i * (Nat.choose (m + 1 + 1) i : ℤ) *
      ((q + 1 - i : ℕ) : ℤ) ^ (m + 1)) (q + 1)]
  rw [Finset.sum_range_succ'
    (fun i => (-1 : ℤ) ^ i * (Nat.choose (m + 1) i : ℤ) *
      ((q + 1 - i : ℕ) : ℤ) ^ m) (q + 1)]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hz : (q + 1 : ℤ) * ((q + 1 : ℕ) : ℤ) ^ m =
    ((q + 1 : ℕ) : ℤ) ^ (m + 1) := by
    push_cast
    rw [pow_succ]
    ring
  have hsum :
    (∑ j ∈ Finset.range (q + 1),
      (-1 : ℤ) ^ (j + 1) * (Nat.choose (m + 2) (j + 1) : ℤ) *
        ((q + 1 - (j + 1) : ℕ) : ℤ) ^ (m + 1)) =
      (∑ j ∈ Finset.range (q + 1),
        (q + 1 : ℤ) * ((-1 : ℤ) ^ (j + 1) *
          (Nat.choose (m + 1) (j + 1) : ℤ) *
            ((q + 1 - (j + 1) : ℕ) : ℤ) ^ m)) +
      ∑ j ∈ Finset.range (q + 1),
        (m + 1 - q : ℕ) * ((-1 : ℤ) ^ j * (Nat.choose (m + 1) j : ℤ) *
          ((q - j : ℕ) : ℤ) ^ m) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hjq : j ≤ q := by omega
    have hjm : j ≤ m + 1 := hjq.trans hq
    have hpas : ((Nat.choose (m + 2) (j + 1) : ℕ) : ℤ) =
      (Nat.choose (m + 1) j : ℤ) + (Nat.choose (m + 1) (j + 1) : ℤ) := by
      exact_mod_cast Nat.choose_succ_succ (m + 1) j
    have hchoose : (Nat.choose (m + 1) (j + 1) : ℤ) * (j + 1 : ℤ) =
      (Nat.choose (m + 1) j : ℤ) * (m + 1 - j : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq (m + 1) j
    simp only [Nat.succ_sub_succ_eq_sub, pow_succ]
    rw [hpas]
    push_cast [Nat.cast_sub hq, Nat.cast_sub hjq, Nat.cast_sub hjm] at hchoose ⊢
    linear_combination
      ((-1 : ℤ) ^ j * ((q : ℤ) - j) ^ m) * hchoose
  rw [hsum, hz]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_coeff_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_coeff_succ_succ (m k : ℕ) (hk : k < m) :
  ehd_coeff (m + 1) (k + 1) =
    (k + 2 : ℤ) * ehd_coeff m (k + 1) + (m - k : ℕ) * ehd_coeff m k := by
  have hq : m - k - 1 ≤ m + 1 := by omega
  have h := ehd_altSum_succ m (m - k - 1) hq
  have h1 : m - k = (m - k - 1) + 1 := by omega
  have h2 : m - (k + 1) = m - k - 1 := by omega
  have h3 : m + 1 - (m - k - 1) = k + 2 := by omega
  have h4 : m + 1 - (k + 1) = m - k := by omega
  unfold ehd_coeff
  rw [h4, h1, h2]
  rw [h3] at h
  push_cast at h ⊢
  linear_combination h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_altSum_succ_self_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
open fwdDiff in
private lemma ehd_altSum_succ_self_zero (m : ℕ) : ehd_altSum m (m + 1) = 0 := by
  have hzero : Δ_[(1 : ℤ)]^[m + 1] (fun r : ℤ => r ^ m) = 0 :=
    fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) (j := m) (n := m + 1) (by omega)
  have h := congrFun hzero (0 : ℤ)
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [Pi.zero_apply, zsmul_eq_mul, zero_add, nsmul_eq_mul, mul_one] at h
  unfold ehd_altSum
  calc
    (∑ i ∈ Finset.range (m + 1 + 1),
      (-1 : ℤ) ^ i * (Nat.choose (m + 1) i : ℤ) *
        ((m + 1 - i : ℕ) : ℤ) ^ m) =
      ∑ x ∈ Finset.range (m + 1 + 1),
        (-1 : ℤ) ^ (m + 1 - x) * (Nat.choose (m + 1) x : ℤ) * (x : ℤ) ^ m := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      have hle : x ≤ m + 1 := by omega
      have hi : m + 1 + 1 - 1 - x = m + 1 - x := by omega
      have hbase : m + 1 - (m + 1 - x) = x := by omega
      rw [hi, hbase, Nat.choose_symm hle]
    _ = 0 := by simpa using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_coeff_succ_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_coeff_succ_self (m : ℕ) : ehd_coeff (m + 1) (m + 1) = 0 := by
  simp [ehd_coeff, ehd_altSum]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_eulerStep_coeff_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_eulerStep_coeff_succ (m k : ℕ) (A : Polynomial ℤ) :
  (((1 + Polynomial.C (m : ℤ) * Polynomial.X) * A +
    Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative A).coeff (k + 1)) =
    (k + 2 : ℤ) * A.coeff (k + 1) + ((m : ℤ) - k) * A.coeff k := by
  rw [show (1 + Polynomial.C (m : ℤ) * Polynomial.X) * A =
    A + Polynomial.C (m : ℤ) * (Polynomial.X * A) by ring]
  rw [show Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative A =
    Polynomial.X * Polynomial.derivative A -
      Polynomial.X * (Polynomial.X * Polynomial.derivative A) by ring]
  cases k with
  | zero =>
    simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_derivative]
    ring
  | succ k =>
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_eulerStep_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_eulerStep_coeff_zero (m : ℕ) (A : Polynomial ℤ) :
  (((1 + Polynomial.C (m : ℤ) * Polynomial.X) * A +
    Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative A).coeff 0) = A.coeff 0 := by
  rw [show (1 + Polynomial.C (m : ℤ) * Polynomial.X) * A =
    A + Polynomial.C (m : ℤ) * (Polynomial.X * A) by ring]
  rw [show Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative A =
    Polynomial.X * Polynomial.derivative A -
      Polynomial.X * (Polynomial.X * Polynomial.derivative A) by ring]
  simp [Polynomial.coeff_add, Polynomial.coeff_sub]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_poly_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_poly_succ (m : ℕ) :
  ehd_poly (m + 1) = (1 + Polynomial.C (m : ℤ) * Polynomial.X) * ehd_poly m +
    Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (ehd_poly m) := by
  ext j
  cases j with
  | zero =>
    rw [ehd_poly_coeff_eq, ehd_eulerStep_coeff_zero]
    simp [ehd_poly_coeff_eq, ehd_coeff_zero]
  | succ k =>
    rw [ehd_poly_coeff_eq, ehd_eulerStep_coeff_succ]
    rw [ehd_poly_coeff_eq m (k + 1), ehd_poly_coeff_eq m k]
    obtain hkm | hkm | hmk := lt_trichotomy k m
    · have hk1 : k + 1 < m + 1 := by omega
      have hk2 : k < m + 1 := by omega
      have hk3 : k + 1 < m + 1 + 1 := by omega
      simp only [hk3, hk1, hk2, ↓reduceIte]
      rw [ehd_coeff_succ_succ m k hkm]
      push_cast [Nat.cast_sub (Nat.le_of_lt hkm)]
      ring
    · subst k
      have hm1 : m + 1 < m + 1 + 1 := by omega
      have hm2 : ¬m + 1 < m + 1 := by omega
      have hm3 : m < m + 1 := by omega
      simp only [hm1, hm2, hm3, ↓reduceIte]
      rw [ehd_coeff_succ_self]
      ring
    · have hk1 : ¬k + 1 < m + 1 + 1 := by omega
      have hk2 : ¬k + 1 < m + 1 := by omega
      have hk3 : ¬k < m + 1 := by omega
      simp only [hk1, hk2, hk3, ↓reduceIte]
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_eq_poly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_eq_poly (P : ℕ → Polynomial ℤ)
  (hP : ∀ m : ℕ, P m =
    ∑ k ∈ Finset.range (m + 1),
      Polynomial.monomial k
        (∑ i ∈ Finset.range (m - k + 1),
          (-1 : ℤ) ^ i * (Nat.choose (m + 1) i : ℤ) *
            ((m - k - i : ℕ) : ℤ) ^ m))
  (m : ℕ) : P m = ehd_poly m := by
  simpa [ehd_poly, ehd_coeff, ehd_altSum] using hP m

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_table_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_table_vanish : ∀ {m k : ℕ}, m < k → ehd_table m k = 0 := by
  intro m
  induction m with
  | zero =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rfl
  | succ m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [ehd_table, ih (show m < k by omega), ih (show m < k + 1 by omega),
      ih (show m < k + 2 by omega)]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_derivStep_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_derivStep_zero (m : ℕ) (hm : 0 < m) (A B C : Polynomial ℤ)
  (h0 : B = Polynomial.C (m : ℤ) * A +
    (1 - Polynomial.X) * Polynomial.derivative A)
  (h1 : Polynomial.C ((2 : ℤ) ^ 2) * C =
    Polynomial.C ((m - 1 : ℕ) : ℤ) * B +
      (1 - Polynomial.X) * Polynomial.derivative B) :
  A + ehd_b 1 * B + ehd_lambda 2 * C =
    Polynomial.C (m + 1 : ℤ) * (A + Polynomial.X * B) +
      (1 - Polynomial.X) * Polynomial.derivative (A + Polynomial.X * B) := by
  unfold ehd_b ehd_lambda
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X]
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at h1 ⊢
  norm_num [map_add, map_sub] at h0 h1 ⊢
  linear_combination h0 + Polynomial.X * h1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_derivStep_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_derivStep_succ (m k : ℕ) (hk0 : 0 < k) (hkm : k < m)
  (R A B C : Polynomial ℤ)
  (hp : Polynomial.C ((k : ℤ) ^ 2) * A =
    Polynomial.C ((m - (k - 1) : ℕ) : ℤ) * R +
      (1 - Polynomial.X) * Polynomial.derivative R)
  (h0 : Polynomial.C ((k + 1 : ℤ) ^ 2) * B =
    Polynomial.C ((m - k : ℕ) : ℤ) * A +
      (1 - Polynomial.X) * Polynomial.derivative A)
  (h1 : Polynomial.C ((k + 2 : ℤ) ^ 2) * C =
    Polynomial.C ((m - (k + 1) : ℕ) : ℤ) * B +
      (1 - Polynomial.X) * Polynomial.derivative B) :
  Polynomial.C ((k + 1 : ℤ) ^ 2) *
    (A + ehd_b (k + 1) * B + ehd_lambda (k + 2) * C) =
    Polynomial.C ((m + 1 - k : ℕ) : ℤ) *
      (R + ehd_b k * A + ehd_lambda (k + 1) * B) +
      (1 - Polynomial.X) *
        Polynomial.derivative (R + ehd_b k * A + ehd_lambda (k + 1) * B) := by
  unfold ehd_b ehd_lambda
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, zero_add]
  have hk1m : k + 1 ≤ m := by omega
  have hkm1 : k - 1 ≤ m := by omega
  have hkle : k ≤ m := by omega
  have hkt : k ≤ m + 1 := by omega
  have hkone : 1 ≤ k := by omega
  push_cast [Nat.cast_sub hkone, Nat.cast_sub hkm1, Nat.cast_sub hkle,
    Nat.cast_sub hk1m, Nat.cast_sub hkt] at hp h0 h1 ⊢
  norm_num [map_add, map_sub, map_pow] at hp h0 h1 ⊢
  linear_combination hp +
    ((k : Polynomial ℤ) + 1 + (k : Polynomial ℤ) * Polynomial.X) * h0 +
    (((k : Polynomial ℤ) + 1) ^ 2 * Polynomial.X) * h1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_derivStep_diag](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_derivStep_diag (m : ℕ) (R : Polynomial ℤ)
  (h : Polynomial.C ((m : ℤ) ^ 2) =
    R + (1 - Polynomial.X) * Polynomial.derivative R) :
  Polynomial.C ((m + 1 : ℤ) ^ 2) =
    R + ehd_b m + (1 - Polynomial.X) * Polynomial.derivative (R + ehd_b m) := by
  unfold ehd_b
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, zero_add]
  norm_num [map_add, map_pow] at h ⊢
  linear_combination h
set_option maxHeartbeats 800000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_table_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_table_deriv : ∀ m k : ℕ,
  Polynomial.C ((k + 1 : ℤ) ^ 2) * ehd_table m (k + 1) =
    Polynomial.C ((m - k : ℕ) : ℤ) * ehd_table m k +
      (1 - Polynomial.X) * Polynomial.derivative (ehd_table m k)
  | 0, k => by
    cases k <;> simp [ehd_table]
  | m + 1, k => by
    by_cases hgt : m + 1 < k
    · rw [ehd_table_vanish hgt, ehd_table_vanish (show m + 1 < k + 1 by omega)]
      simp
    by_cases heq : k = m + 1
    · subst k
      rw [ehd_table_vanish (show m + 1 < m + 1 + 1 by omega), ehd_table_diag]
      simp
    have hle : k ≤ m := by omega
    rcases lt_or_eq_of_le hle with hkm | hkm
    · cases k with
      | zero =>
        have hm : 0 < m := by omega
        have h0 := ehd_table_deriv m 0
        have h1 := ehd_table_deriv m 1
        have hstep := ehd_derivStep_zero m hm (ehd_table m 0) (ehd_table m 1)
          (ehd_table m 2) (by simpa using h0) h1
        simp only [ehd_table]
        norm_num [map_add, map_pow] at hstep ⊢
        exact hstep
      | succ k =>
        have hp := ehd_table_deriv m k
        have h0 := ehd_table_deriv m (k + 1)
        have h1 := ehd_table_deriv m (k + 2)
        have h1' :
          Polynomial.C ((k + 1 + 2 : ℤ) ^ 2) * ehd_table m (k + 3) =
            Polynomial.C ((m - (k + 1 + 1) : ℕ) : ℤ) * ehd_table m (k + 2) +
              (1 - Polynomial.X) * Polynomial.derivative (ehd_table m (k + 2)) :=
  convert h1 using 1
  all_goals norm_num [Nat.cast_add]
  exact Or.inl (by ring)
  have hstep := ehd_derivStep_succ m (k + 1) (by omega) (by omega)
    (ehd_table m k) (ehd_table m (k + 1)) (ehd_table m (k + 2))
    (ehd_table m (k + 3)) (by simpa using hp) h0 h1'
  simpa only [ehd_table, Nat.succ_eq_add_one, add_assoc] using hstep
  · subst k
    cases m with
    | zero => norm_num [ehd_table]
    | succ m =>
      have hraw := ehd_table_deriv (m + 1) m
      rw [ehd_table_diag] at hraw
      have hsub : m + 1 - m = 1 := by omega
      rw [hsub] at hraw
      have h : Polynomial.C (((m + 1 : ℕ) : ℤ) ^ 2) =
        ehd_table (m + 1) m +
          (1 - Polynomial.X) * Polynomial.derivative (ehd_table (m + 1) m) := by
        simpa [Nat.cast_add] using hraw
      have hstep := ehd_derivStep_diag (m + 1) (ehd_table (m + 1) m) h
      have hrow : ehd_table (m + 2) (m + 1) =
        ehd_table (m + 1) m + ehd_b (m + 1) := by
        rw [ehd_table, ehd_table_diag,
          ehd_table_vanish (show m + 1 < m + 2 by omega)]
        ring
      rw [ehd_table_diag, hrow]
      simpa [Nat.cast_add] using hstep

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_table_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_table_zero_succ (m : ℕ) :
  ehd_table (m + 1) 0 =
    (1 + Polynomial.C (m : ℤ) * Polynomial.X) * ehd_table m 0 +
      Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (ehd_table m 0) := by
  rw [ehd_table]
  have h := ehd_table_deriv m 0
  norm_num only [zero_add, Nat.sub_zero, one_pow, map_one, one_mul] at h
  rw [h]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ehd_lambda_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma ehd_lambda_prod : ∀ n : ℕ,
  (∏ j ∈ Finset.range n, ehd_lambda (j + 1) ^ (n - j)) =
    Polynomial.X ^ Nat.choose (n + 1) 2 *
      Polynomial.C (∏ k ∈ Finset.range n, ((Nat.factorial (k + 1) : ℤ) ^ 2))
  | 0 => by simp
  | n + 1 => by
    have hsplit :
      (∏ j ∈ Finset.range (n + 1), ehd_lambda (j + 1) ^ (n + 1 - j)) =
        (∏ j ∈ Finset.range n, ehd_lambda (j + 1) ^ (n - j)) *
          ∏ j ∈ Finset.range (n + 1), ehd_lambda (j + 1) := by
  rw [Finset.prod_range_succ]
  have hlast : ehd_lambda (n + 1) ^ (n + 1 - n) = ehd_lambda (n + 1) := by
    rw [show n + 1 - n = 1 by omega, pow_one]
  rw [hlast]
  have hterm : ∀ j ∈ Finset.range n,
    ehd_lambda (j + 1) ^ (n + 1 - j) =
      ehd_lambda (j + 1) ^ (n - j) * ehd_lambda (j + 1) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib,
    Finset.prod_range_succ]
  ring
  rw [hsplit, ehd_lambda_prod n, ehd_lambda_prod_range,
    Finset.prod_range_succ]
  have hchoose : Nat.choose (n + 2) 2 = Nat.choose (n + 1) 2 + (n + 1) := by
    have hchoose' : Nat.choose (n + 2) 2 =
      (n + 1) + Nat.choose (n + 1) 2 := by
      simpa only [Nat.succ_eq_add_one, Nat.choose_one_right] using
        Nat.choose_succ_succ (n + 1) 1
    omega
  rw [hchoose, pow_add, map_mul]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[eulerianPolynomial_hankelDeterminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
lemma eulerianPolynomial_hankelDeterminant
  {P : ℕ → Polynomial ℤ}
  {n : ℕ}
-- given
  (hP : ∀ m : ℕ, P m = ∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (∑ i ∈ Finset.range (m - k + 1), (-1 : ℤ) ^ i * (Nat.choose (m + 1) i : ℤ) * ((m - k - i : ℕ) : ℤ) ^ m)) :
-- imply
  Matrix.det (fun i j : Fin (n + 1) => P (i.val + j.val)) =
    Polynomial.X ^ Nat.choose (n + 1) 2 *
    Polynomial.C (∏ k ∈ Finset.range n, ((Nat.factorial (k + 1) : ℤ) ^ 2)) := by
-- proof
  calc
    Matrix.det (fun i j : Fin (n + 1) ↦ P (i.val + j.val)) =
      Matrix.det (fun i j : Fin (n + 1) ↦ ehd_poly (i.val + j.val)) := by
        congr 1
        funext i j
        exact ehd_eq_poly P hP (i.val + j.val)
    _ = hankelTransform ehd_poly n := rfl
    _ = ∏ j ∈ Finset.range n, ehd_lambda (j + 1) ^ (n - j) := by
      have hdet := hankelTransform_eq_prod_of_weightedMotzkin
        (K := Polynomial ℤ) (alpha := ehd_b) (beta := ehd_lambda)
        (M := ehd_table) (mu0 := 1)
        (by rfl)
        (by intro j; rfl)
        (by
          intro m
          simp [ehd_table, ehd_b, ehd_lambda])
        (by intro m j; rfl)
        n
      have hzeroColumn : (fun m ↦ ehd_table m 0) = ehd_poly := by
        funext m
        exact ehd_table_zero_eq_poly m
      rw [hzeroColumn] at hdet
      simpa only [one_pow, one_mul] using hdet
    _ = Polynomial.X ^ Nat.choose (n + 1) 2 *
      Polynomial.C (∏ k ∈ Finset.range n, ((Nat.factorial (k + 1) : ℤ) ^ 2)) :=
      ehd_lambda_prod n
end MetaMathlibExt



-- created on 2026-10-20
-- updated on 2026-10-23
