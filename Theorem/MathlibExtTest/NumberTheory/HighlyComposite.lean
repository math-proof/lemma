/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HighlyComposite.lean -/


import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Def.NumberTheory.HighlyComposite
import Lemma.Nat.HighlyComposite


example : Nat.IsHighlyComposite 1 := by simp [Nat.IsHighlyComposite]

example : Nat.IsHighlyComposite 6 := by
  constructor
  · norm_num
  · intro m hm hm6
    interval_cases m <;> norm_num at * <;> decide

example : ¬Nat.IsHighlyComposite 8 := by
  intro h
  have hlt := h.2 6 (by norm_num) (by norm_num)
  have hnot : ¬(6 : ℕ).divisors.card < (8 : ℕ).divisors.card := by decide
  exact hnot hlt

example (h : Nat.IsHighlyComposite 12) : (2 : ℕ) ∣ 12 :=
  h.dvd_of_prime_le (p := 2) (q := 3) (by decide) (by decide) (by decide) (by decide)

example (h : Nat.IsHighlyComposite 36) :
    (36 : ℕ).factorization 3 ≤ (36 : ℕ).factorization 2 :=
  h.factorization_antitone (p := 2) (q := 3) (by decide) (by decide) (by decide)

