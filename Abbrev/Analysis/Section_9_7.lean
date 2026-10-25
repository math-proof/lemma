import Mathlib
import Abbrev.Analysis.Section_9_3.Part2
import Theorem.Analysis.Section_9_4.Part2
/-!
# Analysis I, Section 9.7: The intermediate value theorem

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The intermediate value theorem.
-/


namespace Chapter9

open Classical in
noncomputable abbrev f_9_7_1 : ℝ → ℝ := fun x ↦ if x ≤ 0 then -1 else 1

abbrev f_9_7_2 : ℝ → ℝ := fun x ↦ x^3 - x

end Chapter9
