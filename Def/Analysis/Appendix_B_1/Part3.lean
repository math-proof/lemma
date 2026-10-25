import Mathlib
import Inductive.Analysis.Appendix_B_1
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

def IntDecimal.toInt : IntDecimal → Int
  | zero => 0
  | pos p => p.toNat
  | neg p => -p.toNat

end AppendixB
