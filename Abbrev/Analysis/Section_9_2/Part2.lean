import Mathlib
import Theorem.Analysis.Section_9_2
/-!
# Analysis I, Section 9.2: The algebra of real-valued functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Recalling basic pointwise operations on functions.

-/


namespace Chapter9

abbrev f_9_2_2 : ℝ → ℝ := fun x ↦ x^2

abbrev g_9_2_2 : ℝ → ℝ := fun x ↦ 2*x

end Chapter9
