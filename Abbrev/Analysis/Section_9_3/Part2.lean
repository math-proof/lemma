module
public import Mathlib
public import Mathlib.Data.Real.Sign
public import Theorem.Analysis.Section_9_1.Part3
public import Theorem.Analysis.Section_9_3
set_option doc.verso.suggestions false


public section

namespace Chapter9

noncomputable abbrev f_9_3_17 : ℝ → ℝ := fun x ↦ if x = 0 then 1 else 0

open Classical in
/-- Example 9.3.21 -/
noncomputable abbrev f_9_3_21 : ℝ → ℝ := fun x ↦ if x ∈ (fun q:ℚ ↦ (q:ℝ)) '' .univ then 1 else 0

end Chapter9
