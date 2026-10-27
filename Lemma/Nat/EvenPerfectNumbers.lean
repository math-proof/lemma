import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[sum_divisors_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EvenPerfectNumbers.lean)
-/
@[path]
private lemma sum_divisors_two_pow (k : ℕ) :
  ∑ d ∈ (2 ^ k).divisors, d = 2 ^ (k + 1) - 1 := by
  have h1 : ∑ x ∈ Finset.range (k + 1), 2 ^ x = 2 ^ (k + 1) - 1 := by
    have h2 := Nat.geomSum_eq (m := 2) (by norm_num) (k + 1)
    simpa using h2
  have h0 : (∑ d ∈ (2 ^ k).divisors, d) = ∑ x ∈ Finset.range (k + 1), 2 ^ x :=
    Nat.sum_divisors_prime_pow Nat.prime_two
  rwa [h0]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[euler_characterization_of_even_perfect_numbers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EvenPerfectNumbers.lean)
-/
@[path]
lemma euler_characterization_of_even_perfect_numbers
  {N : ℕ}
-- given
  (hN_even : Even N)
  (hN_perfect : Nat.Perfect N) :
-- imply
  ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (2 ^ p - 1) ∧
    N = 2 ^ (p - 1) * (2 ^ p - 1) := by
-- proof
  obtain ⟨hsum, hpos⟩ := hN_perfect
  obtain ⟨k, m, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (ne_of_gt hpos)
  have hm_ne : m ≠ 0 := by
    rintro rfl
    simp at hpos
  have hk : 1 ≤ k := by
    obtain rfl | h := Nat.eq_zero_or_pos k
    · have hevm : Even m := by simpa using hN_even
      exact absurd hevm (Nat.not_even_iff_odd.mpr hodd)
    · exact h
  have hcop : Nat.Coprime (2 ^ k) m := hodd.coprime_two_right.symm.pow_left k
  have hperf : ∑ d ∈ (2 ^ k * m).divisors, d = 2 * (2 ^ k * m) :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp ⟨hsum, hpos⟩
  set q := 2 ^ (k + 1) - 1 with hq
  have h2k4 : 4 ≤ 2 ^ (k + 1) :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq3 : 3 ≤ q := by omega
  have h2k : 2 ^ (k + 1) = q + 1 := by omega
  have hσ : q * (∑ d ∈ m.divisors, d) = (q + 1) * m := by
    have h1 := Nat.Coprime.sum_divisors_mul hcop
    rw [sum_divisors_two_pow, ← hq, hperf] at h1
    have h2 : 2 * (2 ^ k * m) = (q + 1) * m := by
      rw [← h2k, pow_succ']
      ring
    exact h1.symm.trans h2
  have hqcop : Nat.Coprime q (q + 1) := by simp
  have hqdvd : q ∣ (q + 1) * m := ⟨∑ d ∈ m.divisors, d, hσ.symm⟩
  have hqm : q ∣ m := hqcop.dvd_mul_left.mp hqdvd
  obtain ⟨t, rfl⟩ := hqm
  have ht0 : 0 < t := by
    obtain rfl | h := Nat.eq_zero_or_pos t
    · simp at hm_ne
    · exact h
  have hq0 : q ≠ 0 := by omega
  have hS : ∑ d ∈ (q * t).divisors, d = (q + 1) * t := by
    apply mul_left_cancel₀ hq0
    calc q * ∑ d ∈ (q * t).divisors, d = (q + 1) * (q * t) := hσ
      _ = q * ((q + 1) * t) := by ring
  have hSt : ∑ d ∈ (q * t).divisors, d = q * t + t := by
    rw [hS]
    ring
  have hP : ∑ i ∈ (q * t).properDivisors, i = t := by
    have h := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := q * t)
    omega
  have htm : t < q * t := lt_mul_of_one_lt_left ht0 (by omega)
  have ht_mem : t ∈ (q * t).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨dvd_mul_left t q, htm⟩
  have h1_mem : 1 ∈ (q * t).properDivisors := by
    rw [Nat.one_mem_properDivisors_iff_one_lt]
    have e := Nat.mul_le_mul (by omega : (2 : ℕ) ≤ q) (by omega : (1 : ℕ) ≤ t)
    omega
  have ht1 : t = 1 := by
    by_contra hne
    have hsub : ({1, t} : Finset ℕ) ⊆ (q * t).properDivisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact h1_mem
      · exact ht_mem
    have hle : (1 : ℕ) + t ≤ ∑ i ∈ (q * t).properDivisors, i := by
      calc (1 : ℕ) + t = ∑ x ∈ ({1, t} : Finset ℕ), x :=
        (Finset.sum_pair (f := fun x => x) (Ne.symm hne)).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le i)
    omega
  subst ht1
  rw [mul_one] at hP
  have hq_prime : q.Prime := Nat.sum_properDivisors_eq_one_iff_prime.mp hP
  have hp_prime : (k + 1).Prime := by
    have hM : ((2 : ℕ) ^ (k + 1) - 1).Prime := by
      rwa [← hq]
    exact (Nat.prime_of_pow_sub_one_prime (by omega) hM).2
  refine ⟨k + 1, hp_prime, ?_, ?_⟩
  · rw [← hq]
    exact hq_prime
  · rw [Nat.add_sub_cancel, mul_one, ← hq]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
