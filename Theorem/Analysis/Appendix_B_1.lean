import Mathlib
import Instance.Analysis.Appendix_B_1.Part2
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

theorem Digit.lt (d:Digit) : (d:ℕ) < 10 := d.isLt

end AppendixB
