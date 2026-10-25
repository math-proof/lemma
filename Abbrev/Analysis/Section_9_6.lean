import Mathlib
import Mathlib.Data.Real.Sign
import Abbrev.Analysis.Section_9_3.Part2
import Theorem.Analysis.Section_9_4.Part2
/-!
# Analysis I, Section 9.6: The maximum principle

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuous functions on closed and bounded intervals are bounded.
- Continuous functions on closed and bounded intervals attain their maximum and minimum.
-/


namespace Chapter9

/-- Definition 9.6.1 -/
abbrev BddAboveOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, f x ≤ M

abbrev BddBelowOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, -M ≤ f x

abbrev BddOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, |f x| ≤ M

end Chapter9
