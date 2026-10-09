import sympy.functions.combinatorial.integer_factorials
import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


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
    · rw [if_neg (show ¬(0 ≤ k) by omega), if_neg (show ¬(0 ≤ k + 1) by omega),
        if_neg (show ¬(0 ≤ k + 1) by omega), sub_zero]
    · rw [if_neg (show ¬(0 ≤ k) by omega), hk']
      simp
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [if_pos hk, if_pos (show (0 : ℤ) ≤ m + 1 by omega), if_pos (show (0 : ℤ) ≤ m + 1 by omega), show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast, Int.toNat_natCast, Nat.choose_succ_succ]
    push_cast
    ring


-- created on 2023-06-03
