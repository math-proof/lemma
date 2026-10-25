import Mathlib
import Abbrev.Analysis.Appendix_B_1.Part2
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

@[simp]
theorem Digit.toNat_mk {n:ℕ} (h: n < 10) : (Digit.mk h:ℕ) = n := rfl

@[simp]
theorem Digit.inj (d d':Digit) : d = d' ↔ (d:ℕ) = d' := by grind

theorem Digit.mk_eq_iff (d:Digit) {n:ℕ} (h: n < 10) : d = mk h ↔ (d:ℕ) = n := by
  convert Digit.inj d (mk h)

theorem Digit.eq (n: Digit) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
  fin_cases n <;> simp +decide <;> tauto

end AppendixB
