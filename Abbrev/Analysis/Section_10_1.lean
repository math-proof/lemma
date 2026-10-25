import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorem.Analysis.Section_10_1
/-!
# Analysis I, Section 10.1: Basic definitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`HasDerivWithinAt`, {name}`derivWithin`, and {name}`DifferentiableWithinAt`.

Note that the Mathlib conventions differ slightly from that in the text, in that
differentiability is defined even at points that are not limit points of the domain;
derivatives in such cases may not be unique, but {name}`derivWithin` still selects one such
derivative in such cases (or {lean}`0`, if no derivative exists).

-/


namespace Chapter10

variable (x₀ : ℝ)

abbrev f_10_1_6 : ℝ → ℝ := abs

end Chapter10
