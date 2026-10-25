import Mathlib
import Abbrev.Analysis.Section_4_3


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) (positive case) -/
theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) (negative case) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) (zero case) -/
theorem abs_of_zero : abs 0 = 0 := rfl

end Section_4_3
