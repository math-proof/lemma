/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
/-!
# Jordan totient function

This module defines Jordan's totient function `J_k(n)` from Yuan He,
*On the mean values of products of Dirichlet L-functions at positive
integers*, arXiv:2310.18048v3, equation (1.7) and equation (2.7).

For positive `k` and `n`, `J_k(n) = n^k * ∏_{p ∣ n} (1 - 1 / p^k)`.
We define the integral prime-factorization form and prove the exact
rational Euler product and the integer Möbius divisor sum
`∑_{d ∣ n} μ(n / d) * d^k`. The underlying `ArithmeticFunction` is
extended by `J_k(0) = 0`; the product, Möbius-sum, and rational-product
identities below hold for all `k` whenever `n ≠ 0`, generalizing the
positive-`k` source domain.
-/
namespace ArithmeticFunction
/-- Jordan totient `J_k`, integral factorization form (He (1.7)). -/
def jordanTotient (k : ℕ) : ArithmeticFunction ℕ where
  toFun n :=
    if n = 0 then 0
    else ∏ p ∈ n.primeFactors, p ^ (k * (n.factorization p - 1)) *
      (p ^ k - 1)
  map_zero' := ite_eq_left rfl
/-- Zero extension convention: `J_k(0) = 0`. -/
theorem jordanTotient_zero (k : ℕ) :
    jordanTotient k 0 = 0 := rfl
/-- `J_k(1) = 1` since the product is empty. -/
theorem jordanTotient_apply_one (k : ℕ) :
    jordanTotient k 1 = 1 := by
  simp [jordanTotient, Nat.primeFactors_one]
/-- Unfolding at nonzero `n` (integral form of He (1.7)). -/
theorem jordanTotient_eq_prod_factorization {k n : ℕ}
    (hn : n ≠ 0) :
    jordanTotient k n = ∏ p ∈ n.primeFactors,
      p ^ (k * (n.factorization p - 1)) * (p ^ k - 1) := by
  unfold jordanTotient
  simp [hn]
/-- Value at prime powers. -/
theorem jordanTotient_prime_pow {k p e : ℕ} (hp : p.Prime)
    (he : 0 < e) :
    jordanTotient k (p ^ e) =
      p ^ (k * (e - 1)) * (p ^ k - 1) := by
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hset : (p ^ e).primeFactors = {p} :=
    Nat.primeFactors_prime_pow he.ne' hp
  rw [jordanTotient_eq_prod_factorization hne, hset,
    Finset.prod_singleton, Nat.factorization_pow_self hp]
/-- Value at primes: `J_k(p) = p^k - 1`. -/
theorem jordanTotient_prime {k p : ℕ} (hp : p.Prime) :
    jordanTotient k p = p ^ k - 1 := by
  have h1 := jordanTotient_prime_pow (k := k) hp one_pos
  simpa [pow_one] using h1
/-- Jordan totient is multiplicative. -/
theorem isMultiplicative_jordanTotient (k : ℕ) :
    IsMultiplicative (jordanTotient k) := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨?_, ?_⟩
  · exact jordanTotient_apply_one k
  · intro m n hm hn hmn
    have hmn_ne : m * n ≠ 0 := mul_ne_zero hm hn
    have hunion : (m * n).primeFactors =
        m.primeFactors ∪ n.primeFactors :=
      Nat.primeFactors_mul hm hn
    have hdisj : Disjoint m.primeFactors n.primeFactors := by
      rw [Finset.disjoint_left]
      intro q hqm hqn
      have hqprime := (Nat.mem_primeFactors.mp hqm).1
      have hqdvd_m := (Nat.mem_primeFactors.mp hqm).2.1
      have hqdvd_n := (Nat.mem_primeFactors.mp hqn).2.1
      have hqdvd_gcd : q ∣ Nat.gcd m n :=
        Nat.dvd_gcd hqdvd_m hqdvd_n
      rw [hmn.gcd_eq_one] at hqdvd_gcd
      exact hqprime.ne_one (Nat.dvd_one.mp hqdvd_gcd)
    have hfact_m : ∀ p ∈ m.primeFactors,
        (m * n).factorization p = m.factorization p := by
      intro p hpm
      have h_eq := Nat.factorization_mul hm hn
      have h1 : (m * n).factorization p =
          m.factorization p + n.factorization p := by
        rw [h_eq, Finsupp.add_apply]
      have hz : n.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by
          intro hpdvd
          have hprime := (Nat.mem_primeFactors.mp hpm).1
          have hpn : p ∈ n.primeFactors :=
            hprime.mem_primeFactors hpdvd hn
          exact Finset.disjoint_left.mp hdisj hpm hpn)
      rw [h1, hz, add_zero]
    have hfact_n : ∀ p ∈ n.primeFactors,
        (m * n).factorization p = n.factorization p := by
      intro p hpn
      have h_eq := Nat.factorization_mul hm hn
      have h1 : (m * n).factorization p =
          m.factorization p + n.factorization p := by
        rw [h_eq, Finsupp.add_apply]
      have hz : m.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by
          intro hpdvd
          have hprime := (Nat.mem_primeFactors.mp hpn).1
          have hpm : p ∈ m.primeFactors :=
            hprime.mem_primeFactors hpdvd hm
          exact Finset.disjoint_left.mp hdisj hpm hpn)
      rw [h1, hz, zero_add]
    rw [jordanTotient_eq_prod_factorization hmn_ne,
      jordanTotient_eq_prod_factorization hm,
      jordanTotient_eq_prod_factorization hn, hunion,
      Finset.prod_union hdisj]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hpm
      rw [hfact_m p hpm]
    · apply Finset.prod_congr rfl
      intro p hpn
      rw [hfact_n p hpn]
/-- `J_1` equals Euler totient, including `0` (He (1.7)). -/
theorem jordanTotient_one_apply (n : ℕ) :
    jordanTotient 1 n = n.totient := by
  by_cases hn : n = 0
  · subst hn
    rw [jordanTotient_zero, Nat.totient_zero]
  · have hJ := jordanTotient_eq_prod_factorization (k := 1) hn
    have hT := Nat.totient_eq_prod_factorization hn
    have hsup : n.factorization.support = n.primeFactors :=
      n.support_factorization
    have hprod : n.factorization.prod (fun p k => p ^ (k - 1) * (p - 1)) =
        ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) := by
      rw [← hsup]
      rfl
    rw [hJ, hT, hprod]
    apply Finset.prod_congr rfl
    intro p _
    simp [pow_one]
/-- Convolution with `μ` equals the divisor sum (one orientation). -/
private theorem jordanTotient_conv_eq_sum {k n : ℕ} (hn : n ≠ 0) :
    (((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * moebius) n =
      ∑ d ∈ n.divisors, moebius (n / d) * (d : ℤ) ^ k := by
  have h1 : ((((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * moebius) n) =
      ∑ x ∈ n.divisorsAntidiagonal,
        (fun a b => (((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) a *
          moebius b)) x.1 x.2 :=
    ArithmeticFunction.mul_apply
  rw [h1, Nat.sum_divisorsAntidiagonal
    (fun a b => (((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) a *
      moebius b))]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := by
    intro h0
    subst h0
    have hmem : (0 : ℕ) ∣ n := hdvd
    simp only [zero_dvd_iff] at hmem
    exact hn hmem
  have hpow : (((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) d) =
      ((d : ℤ) ^ k) := by
    have hcast : ((((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) d)) =
        ((pow k d : ℕ) : ℤ) := rfl
    rw [hcast, pow_apply, ite_eq_right (by simp [hd0]), Nat.cast_pow]
  change (((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) d *
      moebius (n / d)) = _
  rw [hpow, mul_comm]
/-- Agreement at prime powers between convolution and `J`. -/
private theorem jordanTotient_prime_conv_eq {k p e : ℕ} (hp : p.Prime) :
    (((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * moebius) (p ^ (e + 1)) =
      ((jordanTotient k (p ^ (e + 1)) : ℕ) : ℤ) := by
  have hne : p ^ (e + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hppos : 0 < p := hp.pos
  have hJ := jordanTotient_prime_pow (k := k) hp (by omega : 0 < e + 1)
  have h1k : 1 ≤ p ^ k := Nat.one_le_pow k p hppos
  have hcast : ((p ^ (k * e) * (p ^ k - 1) : ℕ) : ℤ) =
      (p : ℤ) ^ (k * e) * ((p : ℤ) ^ k - 1) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h1k, Nat.cast_pow,
      Nat.cast_one]
  have hsub : (e + 1) - 1 = e := Nat.add_sub_cancel e 1
  have hvanish : ∀ i ∈ Finset.range e,
      moebius (p ^ (e + 1) / p ^ i) * ((((p ^ i : ℕ)) : ℤ) ^ k) = 0 := by
    intro i hi
    have hlt : i < e := Finset.mem_range.mp hi
    have hle : i ≤ e + 1 := by omega
    have hexp_ne0 : e + 1 - i ≠ 0 := by omega
    have hexp_ne1 : e + 1 - i ≠ 1 := by omega
    have hdiv : p ^ (e + 1) / p ^ i = p ^ (e + 1 - i) :=
      Nat.pow_div hle hppos
    rw [hdiv, moebius_apply_prime_pow hp hexp_ne0, ite_eq_right hexp_ne1,
      zero_mul]
  have hfe1 : p ^ (e + 1) / p ^ (e + 1) = 1 :=
    Nat.div_self (pow_pos hppos (e + 1))
  have hfe : p ^ (e + 1) / p ^ e = p := by
    have hdiv := Nat.pow_div (Nat.le_succ e) hppos
    rw [show e + 1 - e = 1 by omega, pow_one] at hdiv
    exact hdiv
  have hmoeb_one : moebius 1 = 1 := moebius_apply_one
  have hmoeb_p : moebius p = -1 := moebius_apply_prime hp
  have hcast_e : ((((p ^ e : ℕ)) : ℤ) ^ k) = (p : ℤ) ^ (e * k) := by
    rw [Nat.cast_pow, ← pow_mul]
  have hcast_succ : ((((p ^ (e + 1) : ℕ)) : ℤ) ^ k) =
      (p : ℤ) ^ ((e + 1) * k) := by
    rw [Nat.cast_pow, ← pow_mul]
  have hexp1 : (e + 1) * k = e * k + k := by ring
  have hexp2 : k * e = e * k := by ring
  rw [hJ, hsub, hcast, jordanTotient_conv_eq_sum hne,
    Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero hvanish, zero_add, hfe1, hfe, hmoeb_one,
    hmoeb_p, one_mul, neg_mul, one_mul, hcast_e, hcast_succ, hexp1,
    hexp2, pow_add]
  ring
/-- Source Möbius sum with orientation `μ(n/d) * d^k` (He (2.7)).

Holds for every `k` when `n ≠ 0`, generalizing the positive-`k` source
statement; the hypothesis `0 < k` is therefore omitted. -/
theorem jordanTotient_eq_sum_moebius {k n : ℕ} (hn : n ≠ 0) :
    ((jordanTotient k n : ℕ) : ℤ) =
      ∑ d ∈ n.divisors, moebius (n / d) * (d : ℤ) ^ k := by
  have hJ : IsMultiplicative
      (((jordanTotient k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) :=
    (isMultiplicative_jordanTotient k).natCast
  have hF : IsMultiplicative
      ((((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) * moebius) :=
    IsMultiplicative.mul (isMultiplicative_pow.natCast) isMultiplicative_moebius
  have hEq : (((jordanTotient k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) =
      ((((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) * moebius) := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ hJ _ hF]
    intro p i hp
    by_cases hi : i = 0
    · subst hi
      rw [pow_zero, hJ.map_one, hF.map_one]
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      exact (jordanTotient_prime_conv_eq hp).symm
  calc ((jordanTotient k n : ℕ) : ℤ)
      = ((((jordanTotient k : ArithmeticFunction ℕ) :
        ArithmeticFunction ℤ)) n) := rfl
    _ = (((((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) *
        moebius) n) := by rw [hEq]
    _ = ∑ d ∈ n.divisors, moebius (n / d) * (d : ℤ) ^ k :=
        jordanTotient_conv_eq_sum hn
/-- Cleared-denominator product identity (integral He (1.7)). -/
theorem jordanTotient_mul_prod_primeFactors_pow {k n : ℕ}
    (hn : n ≠ 0) :
    jordanTotient k n * ∏ p ∈ n.primeFactors, p ^ k =
      n ^ k * ∏ p ∈ n.primeFactors, (p ^ k - 1) := by
  rw [jordanTotient_eq_prod_factorization hn]
  have hprod := Nat.prod_primeFactors_pow_factorization hn
  have hnk : (∏ p ∈ n.primeFactors, p ^ n.factorization p) ^ k =
      ∏ p ∈ n.primeFactors, (p ^ n.factorization p) ^ k :=
    (Finset.prod_pow _ _ _).symm
  rw [← hprod] at hnk
  rw [hnk, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpm
  have hprime := (Nat.mem_primeFactors.mp hpm).1
  have hdvd := (Nat.mem_primeFactors.mp hpm).2.1
  have hepos : 0 < n.factorization p :=
    hprime.factorization_pos_of_dvd hn hdvd
  have hke : k * n.factorization p =
      k * (n.factorization p - 1) + k := by
    conv_lhs => rw [← Nat.sub_add_cancel hepos, Nat.mul_add, Nat.mul_one]
  have hpow : p ^ (k * (n.factorization p - 1)) * p ^ k =
      (p ^ n.factorization p) ^ k := by
    rw [← pow_add, ← hke, Nat.mul_comm k _, pow_mul]
  calc p ^ (k * (n.factorization p - 1)) * (p ^ k - 1) * p ^ k
      = (p ^ (k * (n.factorization p - 1)) * p ^ k) * (p ^ k - 1) := by
        ring
    _ = (p ^ n.factorization p) ^ k * (p ^ k - 1) := by rw [hpow]
/-- Exact rational Euler product (He (1.7)).

Holds for every `k` when `n ≠ 0`, generalizing the positive-`k` source
statement; the hypothesis `0 < k` is therefore omitted. -/
theorem jordanTotient_eq_rational_prod {k n : ℕ} (hn : n ≠ 0) :
    ((jordanTotient k n : ℕ) : ℚ) =
      (n : ℚ) ^ k *
        ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ k) := by
  have hclear := jordanTotient_mul_prod_primeFactors_pow (k := k) hn
  have hcast : ((jordanTotient k n : ℕ) : ℚ) *
      ∏ p ∈ n.primeFactors, (p : ℚ) ^ k =
      (n : ℚ) ^ k *
        ∏ p ∈ n.primeFactors, ((p : ℚ) ^ k - 1) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hclear
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] at h
    have hsub : ∀ p ∈ n.primeFactors,
        ((p ^ k - 1 : ℕ) : ℚ) = (p : ℚ) ^ k - 1 := by
      intro p hpm
      have hprime := (Nat.mem_primeFactors.mp hpm).1
      have h1k : 1 ≤ p ^ k := Nat.one_le_pow k p hprime.pos
      rw [Nat.cast_sub h1k, Nat.cast_pow, Nat.cast_one]
    have hprod : (∏ p ∈ n.primeFactors, ((p ^ k - 1 : ℕ) : ℚ)) =
        ∏ p ∈ n.primeFactors, ((p : ℚ) ^ k - 1) :=
      Finset.prod_congr rfl (fun p hpm => hsub p hpm)
    rw [hprod] at h
    exact h
  have hne_prod : ∏ p ∈ n.primeFactors, (p : ℚ) ^ k ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hpm
    have hprime := (Nat.mem_primeFactors.mp hpm).1
    have hp0 : (p : ℚ) ≠ 0 := by
      exact_mod_cast hprime.ne_zero
    exact pow_ne_zero _ hp0
  have hprod_eq : ∏ p ∈ n.primeFactors,
      (1 - 1 / (p : ℚ) ^ k) =
      (∏ p ∈ n.primeFactors, ((p : ℚ) ^ k - 1)) /
        ∏ p ∈ n.primeFactors, (p : ℚ) ^ k := by
    have hterm : ∀ p ∈ n.primeFactors,
        (1 - 1 / (p : ℚ) ^ k) = ((p : ℚ) ^ k - 1) / (p : ℚ) ^ k := by
      intro p hpm
      have hprime := (Nat.mem_primeFactors.mp hpm).1
      have hpk : (p : ℚ) ^ k ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast hprime.ne_zero)
      rw [eq_div_iff hpk, sub_mul, one_mul, one_div_mul_cancel hpk]
    calc ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ k)
        = ∏ p ∈ n.primeFactors, (((p : ℚ) ^ k - 1) / (p : ℚ) ^ k) :=
          Finset.prod_congr rfl (fun p hpm => hterm p hpm)
      _ = (∏ p ∈ n.primeFactors, ((p : ℚ) ^ k - 1)) /
          ∏ p ∈ n.primeFactors, (p : ℚ) ^ k :=
          Finset.prod_div_distrib _ _
  rw [hprod_eq, ← mul_div_assoc, eq_div_iff hne_prod]
  exact hcast
end ArithmeticFunction
