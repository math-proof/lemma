import Mathlib
import Theorem.Analysis.Appendix_B_1.Part7
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

abbrev PosintDecimal.digit (p:PosintDecimal) (i:ℕ) : Digit :=
  if h: i < p.digits.length then p.digits[p.digits.length - i - 1] else 0

abbrev PosintDecimal.carry (p q:PosintDecimal) : ℕ → ℕ := Nat.rec 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1)

end AppendixB
