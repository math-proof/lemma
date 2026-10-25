import Mathlib
import Abbrev.Analysis.Appendix_B_1.Part3
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

theorem PosintDecimal.head_ne_zero (p:PosintDecimal) : p.head ≠ 0 := p.nonzero

theorem PosintDecimal.head_ne_zero' (p:PosintDecimal) : (p.head:ℕ) ≠ 0 := by
  by_contra!
  apply head_ne_zero p
  simp_all [Digit.toNat, Digit.inj]; rfl

theorem PosintDecimal.length_pos (p:PosintDecimal) : 0 < p.digits.length := by
  simp [List.length_pos_iff, p.nonempty]

end AppendixB
