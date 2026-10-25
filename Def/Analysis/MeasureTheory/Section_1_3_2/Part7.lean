import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part6
set_option doc.verso.suggestions false


namespace Remark_1_3_10

/-- Binary-to-ternary function: g(x) = ∑ 2·bⱼ(x)·3^(-j), monotone on \[0,1\], g(\[0,1\]) ⊆ C ∪ \{0\}. -/
noncomputable def binaryToTernary : ℝ → ℝ := Classical.choose binaryToTernary_exists

end Remark_1_3_10
