import Mathlib.Data.Nat.Choose.Sum
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i : ℕ}
-- given
  (h : i ≤ n) :
-- imply
  ∑ k ∈ Finset.Ico i (n + 1), (-1 : ℤ) ^ (k - i) * ((Nat.factorial n / (Nat.factorial i * Nat.factorial (k - i) * Nat.factorial (n - k)) : ℕ) : ℤ) =
      if n = i then 1 else 0 := by
-- proof
  have key : ∀ k ∈ Finset.Ico i (n + 1), Nat.factorial n / (Nat.factorial i * Nat.factorial (k - i) * Nat.factorial (n - k)) = n.choose i * (n - i).choose (k - i) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    have e1 := Nat.choose_mul_factorial_mul_factorial h
    have e2 := Nat.choose_mul_factorial_mul_factorial (show k - i ≤ n - i by omega)
    rw [show n - i - (k - i) = n - k by omega] at e2
    rw [← e1, ← e2]
    ring
  rw [Finset.sum_congr rfl (fun k hk => congrArg (fun m : ℕ => (-1 : ℤ) ^ (k - i) * (m : ℤ)) (key k hk)),
    Finset.sum_Ico_eq_sum_range]
  simp_rw [Nat.add_sub_cancel_left]
  rw [show n + 1 - i = n - i + 1 by omega]
  have alt := Int.alternating_sum_range_choose (n := n - i)
  calc ∑ k ∈ Finset.range (n - i + 1), (-1 : ℤ) ^ k * ((n.choose i * (n - i).choose k : ℕ) : ℤ)
      = (n.choose i : ℤ) * ∑ k ∈ Finset.range (n - i + 1), (-1 : ℤ) ^ k * ((n - i).choose k : ℤ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
    _ = if n = i then 1 else 0 := by
        rw [alt]
        by_cases hni : n = i
        · subst hni
          simp
        · rw [if_neg (by omega), if_neg hni, mul_zero]


-- created on 2023-08-20
