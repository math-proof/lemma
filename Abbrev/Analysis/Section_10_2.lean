import Mathlib
import Theorem.Analysis.Section_9_6
import Theorem.Analysis.Section_10_2
open Chapter9
/-!
# Analysis I, Section 10.2: Local maxima, local minima, and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relation between local extrema and derivatives.
- Rolle's theorem.
- mean value theorem.

-/


namespace Chapter10

/-- Example 10.2.3 -/
abbrev f_10_2_3 : ℝ → ℝ := fun x ↦ x^2 - x^4

end Chapter10
