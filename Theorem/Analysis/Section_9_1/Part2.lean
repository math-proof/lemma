import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import Abbrev.Analysis.Section_6_4.Part3
import Abbrev.Analysis.Section_9_1.Part2
variable (I : Type*)
/-!
# Analysis I, Section 9.1: Subsets of the real line

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib intervals.
- Adherent points, limit points, isolated points.
- Closed sets and closure.
- The Heine-Borel theorem for the real line.

-/


namespace Chapter9

/-- Identification with Mathlib's {name}`AccPt` -/
theorem LimitPt.iff_AccPt (x:ℝ) (X: Set ℝ) : LimitPt x X ↔ AccPt x (.principal X) := by
  rw [accPt_principal_iff_clusterPt,←AdherentPt_def]

end Chapter9
