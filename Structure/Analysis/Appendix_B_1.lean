import Mathlib
import Theorem.Analysis.Appendix_B_1.Part2
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

/-- Definition B.1.2 -/
structure PosintDecimal where
  digits : List Digit
  nonempty : digits ≠ []
  nonzero : digits.head nonempty ≠ 0

end AppendixB
