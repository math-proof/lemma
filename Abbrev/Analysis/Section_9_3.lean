import Mathlib
import Mathlib.Data.Real.Sign
import Theorem.Analysis.Section_9_1.Part3
set_option doc.verso.suggestions false


/-!
# Analysis I, Section 9.3: Limiting values of functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Limits of continuous functions
- Connection with Mathlib's filter convergence concepts
- Limit laws for functions

Technical point: in the text, the functions `f` studied are defined only on subsets `X` of {lean}`ℝ`, and
left undefined elsewhere.  However, in Lean, this then creates some fiddly conversions when trying
to restrict `f` to various subsets of `X` (which, technically, are not precisely subsets of {lean}`ℝ`,
though they can be coerced to such).  To avoid this issue we will deviate from the text by having
our functions defined on all of {lean}`ℝ` (with the understanding that they are assigned "junk" values
outside of the domain `X` of interest).
-/

/-- Definition 9.3.1
Note the books uses ≤ instead of <, but < matches mathlib's definition of neighborhood.
-/
abbrev Real.CloseFn (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) : Prop :=
  ∀ x ∈ X, |f x - L| < ε

/-- Definition 9.3.3 -/
abbrev Real.CloseNear (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop :=
  ∃ δ > 0, ε.CloseFn (X ∩ .Ioo (x₀-δ) (x₀+δ)) f L

namespace Chapter9

/-- Example 9.3.2
Slight change from the book to accomodate the change to {lean}`Real.CloseFn`
-/
abbrev Convergesto (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop := ∀ ε > (0:ℝ), ε.CloseNear X f L x₀

end Chapter9
