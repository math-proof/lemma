import Mathlib
import Abbrev.Analysis.Appendix_B_1.Part6
import Instance.Analysis.Appendix_B_2.Part2
/-!
# Analysis I, Appendix B.2: The decimal representation of real numbers

An implementation of the decimal representation of Mathlib's real numbers {lean}`ℝ`.

This is separate from the way decimal numerals are already represented in Mathlib.  We also represent the integer part of the natural numbers just by {lean}`ℕ`, avoiding using the decimal representation from the
previous section, although we still retain the {name}`AppendixB.Digit` class.
-/


namespace AppendixB

open NNReal NNRealDecimal

theorem RealDecimal.surj (x:ℝ) : ∃ d:RealDecimal, x = d := by
  obtain h | h := le_or_gt 0 x
  . choose d hd using NNRealDecimal.surj (x.toNNReal); use pos d; simp [←hd, h]
  . choose d hd using NNRealDecimal.surj ((-x).toNNReal); use neg d; simp [←hd, show 0 ≤ -x by linarith]

end AppendixB
