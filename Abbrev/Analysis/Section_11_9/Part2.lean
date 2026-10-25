import Mathlib
import Mathlib.Topology.ContinuousOn
import Theorem.Analysis.Section_7_3
import Theorem.Analysis.Section_9_4.Part2
import Abbrev.Analysis.Section_9_8
import Theorem.Analysis.Section_10_1.Part2
import Abbrev.Analysis.Section_10_2
import Theorem.Analysis.Section_11_6
import Abbrev.Analysis.Section_11_8.Part7
import Theorem.Analysis.Section_11_9.Part2
/-!
# Analysis I, Section 11.9: The two fundamental theorems of calculus

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- The fundamental theorems of calculus.
-/


namespace Chapter11

open Chapter9 Chapter10 BoundedInterval

/-- Definition 11.9.3.  We drop the requirement that x be a limit point as this makes
    the Lean arguments slightly cleaner -/
abbrev AntiderivOn (F f: ℝ → ℝ) (I: BoundedInterval) :=
  DifferentiableOn ℝ F I ∧ ∀ x ∈ I, HasDerivWithinAt F (f x) I x

end Chapter11
