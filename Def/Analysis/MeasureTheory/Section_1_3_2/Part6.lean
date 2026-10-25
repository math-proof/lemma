import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Structure.Analysis.MeasureTheory.Section_1_3_2
set_option doc.verso.suggestions false


namespace Remark_1_3_10

/-- The binary-to-ternary function: g(x) = ∑\_\{j≥1\} 2·bⱼ(x)·3^(-j) for x ∈ \[0,1\], else 0. -/
noncomputable def binaryToTernaryFn (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0:ℝ) 1 then
    ∑' j : ℕ, (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
  else 0

end Remark_1_3_10
