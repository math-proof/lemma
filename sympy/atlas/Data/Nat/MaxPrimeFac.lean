/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Lattice.Nat

namespace Nat

/-- The greatest prime divisor of a natural number.

This is totalized by the convention `maxPrimeFac 0 = 0` and `maxPrimeFac 1 = 0`. The value at
zero is only a computational convention: every prime divides zero, so zero has no greatest prime
divisor. The value at one records that one has no prime divisors. -/
def maxPrimeFac (n : ℕ) : ℕ := n.primeFactors.sup id

example : maxPrimeFac 0 = 0 := by decide +kernel
example : maxPrimeFac 1 = 0 := by decide +kernel
example : maxPrimeFac 12 = 3 := by decide +kernel
example : maxPrimeFac 97 = 97 := by decide +kernel
example : maxPrimeFac 125 = 5 := by decide +kernel
example : maxPrimeFac 360 = 5 := by decide +kernel

@[simp]
lemma maxPrimeFac_zero :
    maxPrimeFac 0 = 0 := by
  simp [maxPrimeFac]

@[simp]
lemma maxPrimeFac_one :
    maxPrimeFac 1 = 0 := by
  simp [maxPrimeFac]

lemma prime_maxPrimeFac_of_one_lt (n : ℕ) (h : 1 < n) :
    Nat.Prime (maxPrimeFac n) := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h
  obtain ⟨a, hmem, heq⟩ := Finset.exists_mem_eq_sup n.primeFactors hne id
  have hprime : a.Prime := (Nat.mem_primeFactors.mp hmem).1
  rw [maxPrimeFac, heq]
  exact hprime

/-- The greatest prime factor of a natural number different from `1` divides it. -/
lemma maxPrimeFac_dvd {n : ℕ} (hn : n ≠ 1) : maxPrimeFac n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hlt : 1 < n := by omega
    obtain ⟨a, hmem, heq⟩ :=
      Finset.exists_mem_eq_sup n.primeFactors (Nat.nonempty_primeFactors.mpr hlt) id
    have hdvd : a ∣ n := (Nat.mem_primeFactors.mp hmem).2.1
    rw [maxPrimeFac, heq]
    exact hdvd

/-- Every prime factor of a nonzero natural number is at most its greatest prime factor. -/
lemma le_maxPrimeFac
    {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n := by
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, h_dvd, hn⟩
  have hle : id p ≤ n.primeFactors.sup id := Finset.le_sup hmem
  simpa [maxPrimeFac] using hle

lemma maxPrimeFac_eq_of_dvd_of_le
    (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n) (h_le : maxPrimeFac n ≤ p) :
    maxPrimeFac n = p := by
  exact le_antisymm h_le (le_maxPrimeFac hn.ne' hp h_dvd)

/-- The greatest prime factor of a prime is the prime itself. -/
@[simp]
lemma Prime.maxPrimeFac_eq_self {p : ℕ} (hp : p.Prime) :
    maxPrimeFac p = p := by
  apply maxPrimeFac_eq_of_dvd_of_le p p hp.pos hp (dvd_refl p)
  exact Nat.le_of_dvd hp.pos (maxPrimeFac_dvd hp.ne_one)

/-- The fixed points of `maxPrimeFac` are zero and the primes. -/
@[simp]
lemma maxPrimeFac_eq_self_iff {n : ℕ} :
    maxPrimeFac n = n ↔ n = 0 ∨ n.Prime := by
  constructor
  · intro h
    rcases eq_or_ne n 0 with rfl | hn0
    · exact Or.inl rfl
    · rcases eq_or_ne n 1 with rfl | hn1
      · simp at h
      · have hlt : 1 < n := by omega
        exact Or.inr (h ▸ prime_maxPrimeFac_of_one_lt n hlt)
  · rintro (rfl | hn)
    · simp
    · exact hn.maxPrimeFac_eq_self

/-- The greatest prime factor of a product of nonzero natural numbers is the maximum of their
greatest prime factors. -/
lemma maxPrimeFac_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    maxPrimeFac (m * n) = max (maxPrimeFac m) (maxPrimeFac n) := by
  obtain rfl | hm_lt : m = 1 ∨ 1 < m := by omega
  · simp only [one_mul, maxPrimeFac_one]
    exact (max_eq_right (Nat.zero_le _)).symm
  obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
  · simp only [mul_one, maxPrimeFac_one]
    exact (max_eq_left (Nat.zero_le _)).symm
  have hmn_lt : 1 < m * n := Nat.one_lt_mul_iff.mpr
    ⟨zero_lt_of_lt hm_lt, zero_lt_of_lt hn_lt, Or.inl hm_lt⟩
  apply le_antisymm
  · have hp : Nat.Prime (maxPrimeFac (m * n)) :=
      prime_maxPrimeFac_of_one_lt (m * n) hmn_lt
    rcases hp.dvd_mul.mp (maxPrimeFac_dvd (ne_of_gt hmn_lt)) with hpm | hpn
    · exact (le_maxPrimeFac hm hp hpm).trans (le_max_left _ _)
    · exact (le_maxPrimeFac hn hp hpn).trans (le_max_right _ _)
  · apply max_le
    · have hp : Nat.Prime (maxPrimeFac m) := prime_maxPrimeFac_of_one_lt m hm_lt
      apply le_maxPrimeFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_left (maxPrimeFac_dvd (ne_of_gt hm_lt)) n
    · have hp : Nat.Prime (maxPrimeFac n) := prime_maxPrimeFac_of_one_lt n hn_lt
      apply le_maxPrimeFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_right (maxPrimeFac_dvd (ne_of_gt hn_lt)) m

/-- The greatest prime factor of a nonzero power is the greatest prime factor of its base. -/
@[simp]
lemma maxPrimeFac_pow {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    maxPrimeFac (n ^ k) = maxPrimeFac n :=
  match k, hk with
  | k + 1, _ => by
    by_cases hn : n = 0
    · subst n
      simp
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, maxPrimeFac_mul (pow_ne_zero _ hn) hn, ih (by omega)]
        simp

/-- The greatest prime factor of a natural number is at most that number. -/
lemma maxPrimeFac_le {n : ℕ} : maxPrimeFac n ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (maxPrimeFac_dvd hn1)

/-- The greatest prime factor of a natural number greater than one is the least upper bound of
its prime factors. -/
lemma isLeast_maxPrimeFac {n : ℕ} (hn : 1 < n) :
    IsLeast (upperBounds {p : ℕ | p.Prime ∧ p ∣ n}) (maxPrimeFac n) := by
  constructor
  · rintro p ⟨hp, h_dvd⟩
    exact le_maxPrimeFac (zero_lt_of_lt hn).ne' hp h_dvd
  · intro b hb
    exact hb ⟨prime_maxPrimeFac_of_one_lt n hn, maxPrimeFac_dvd (ne_of_gt hn)⟩

/-- For `n > 1`, the computable greatest prime factor agrees with the supremum of the prime
factors of `n`. -/
lemma maxPrimeFac_eq_sSup {n : ℕ} (hn : 1 < n) :
    maxPrimeFac n = sSup {p : ℕ | p.Prime ∧ p ∣ n} := by
  have h_lub : IsLUB {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) :=
    isLeast_maxPrimeFac hn
  exact (h_lub.csSup_eq
    ⟨maxPrimeFac n, prime_maxPrimeFac_of_one_lt n hn,
      maxPrimeFac_dvd (ne_of_gt hn)⟩).symm

@[simp]
lemma one_lt_maxPrimeFac_iff (n : ℕ) :
    1 < maxPrimeFac n ↔ 1 < n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · simp only [lt_one_iff] at hn
    simp [hn]
  · simp
  · simpa [hn] using (prime_maxPrimeFac_of_one_lt n hn).one_lt

end Nat
