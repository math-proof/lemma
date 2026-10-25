import Mathlib
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

open Classical in
noncomputable abbrev function_example : ℝ → ℝ := fun x ↦ if x ∈ ((fun y:ℚ ↦ (y:ℝ)) '' .univ) then 1 else 0

end Chapter9
