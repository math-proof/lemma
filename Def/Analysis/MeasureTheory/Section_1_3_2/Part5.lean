import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part4
set_option doc.verso.suggestions false


/-- Binary digit extraction: bⱼ(x) = ⌊2^j · x⌋ mod 2.
    For x ∈ \[0,1), this extracts the j-th binary digit.
    Special case: x = 1 has all digits = 1 (1 = 0.111...₂).
    For x ∉ \[0,1\], all digits are 0. -/
noncomputable def binaryDigit (x : ℝ) (j : ℕ) : ℕ :=
  if x ∈ Set.Ico (0:ℝ) 1 then ⌊(2:ℝ)^j * x⌋₊ % 2
  else if x = 1 then 1
  else 0

