/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimePowerFactorizationSum.lean -/

import Mathlib.Data.Nat.Factorization.Defs

namespace MetaMathlibExt

/-! # Prime-power fixed points of prime-factor power sums
-/

/--
A prime power `y = p ^ m` is fixed by the sum of the `s`-th powers of its prime
factors, counted with multiplicity, exactly when `m = p ^ k` and
`s = p ^ k - k` for some natural number `k`.

Source: Spencer P. Hurd and Judson S. McCranie, "Integers That Are Sums of
Uniform Powers of All Their Prime Factors: The Sequence A068916," Journal of
Integer Sequences 22 (2019), Article 19.3.4, Theorem 1 (label origThm1),
lines 187–189,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Hurd/hurd1.tex

`y.factorization.sum fun q e => e * q ^ s` is the paper's `T_s(y)`; for
`y = p ^ m` this is `m * p ^ s`, and `m * p ^ s = p ^ m` forces `m` to be a
power of `p`.
Proves `Wanted` entry `prime_power_factorization_sum_eq_iff`.
-/
theorem prime_power_factorization_sum_eq_iff
    {p m s y : ℕ} (hp : Nat.Prime p) (hm : 0 < m) (hs : 0 < s)
    (hy : y = p ^ m) :
    (y.factorization.sum fun q e => e * q ^ s) = y ↔
      ∃ k : ℕ, m = p ^ k ∧ s = p ^ k - k := by
  have hp2 : 2 ≤ p := hp.two_le
  have hsum : y.factorization.sum (fun q e => e * q ^ s) = m * p ^ s := by
    rw [hy, hp.factorization_pow]
    rw [Finsupp.sum_single_index (by simp)]
  rw [hsum]
  constructor
  · intro h
    have hpm : m * p ^ s = p ^ m := by rw [hy] at h; exact h
    have hdvd : m ∣ p ^ m := ⟨p ^ s, hpm.symm⟩
    obtain ⟨k, _, hmk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    refine ⟨k, hmk, ?_⟩
    have h2 : p ^ (k + s) = p ^ (p ^ k) := by
      rw [pow_add]
      rw [hmk] at hpm
      exact hpm
    have hks : k + s = p ^ k := Nat.pow_right_injective hp2 h2
    have hle : k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
    omega
  · rintro ⟨k, rfl, rfl⟩
    have hle : k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
    rw [hy, ← pow_add, Nat.add_sub_cancel' hle]

end MetaMathlibExt
