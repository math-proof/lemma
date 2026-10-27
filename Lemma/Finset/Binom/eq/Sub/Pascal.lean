import Def.Data.Nat.Factorial.IntegerFactorials
import Mathlib.RingTheory.Polynomial.Pochhammer
import Theorem.Data.Set.Sets


@[path]
private lemma main
  {n : ℕ}
  {k : ℤ}
-- given
  (_h : n > 0) :
-- imply
  Binomial n k = Binomial (n + 1) (k + 1) - Binomial n (k + 1) := by
-- proof
  unfold Binomial
  rcases lt_or_ge k 0 with hk | hk
  · rcases lt_or_eq_of_le (show k + 1 ≤ 0 by omega) with hk' | hk'
    · rw [ite_eq_right (show ¬(0 ≤ k) by omega), ite_eq_right (show ¬(0 ≤ k + 1) by omega),
        ite_eq_right (show ¬(0 ≤ k + 1) by omega), sub_zero]
    · rw [ite_eq_right (show ¬(0 ≤ k) by omega), hk']
      simp
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [ite_eq_left hk, ite_eq_left (show (0 : ℤ) ≤ m + 1 by omega), ite_eq_left (show (0 : ℤ) ≤ m + 1 by omega), show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast, Int.toNat_natCast, Nat.choose_succ_succ]
    push_cast
    ring


-- created on 2023-06-03
