import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[prime_power_factorization_sum_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimePowerFactorizationSum.lean)
-/
@[path]
lemma prime_power_factorization_sum_eq_iff
  {p m s y : ℕ}
-- given
  (hp : Nat.Prime p)
  (hm : 0 < m)
  (hs : 0 < s)
  (hy : y = p ^ m) :
-- imply
  (y.factorization.sum fun q e => e * q ^ s) = y ↔
      ∃ k : ℕ, m = p ^ k ∧ s = p ^ k - k := by
-- proof
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
      rwa [hmk] at hpm
    have hks : k + s = p ^ k := Nat.pow_right_injective hp2 h2
    have hle : k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
    omega
  · rintro ⟨k, rfl, rfl⟩
    have hle : k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
    rw [hy, ← pow_add, Nat.add_sub_cancel' hle]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
