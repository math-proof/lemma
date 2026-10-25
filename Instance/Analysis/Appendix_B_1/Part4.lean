import Mathlib
import Def.Analysis.Appendix_B_1.Part3
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

instance IntDecimal.instCoeInt : Coe IntDecimal Int where
  coe := toInt

end AppendixB
