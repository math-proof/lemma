import Mathlib
import Mathlib.Data.Real.Sign
import Mathlib.Topology.ContinuousOn
import Abbrev.Analysis.Section_9_3.Part2
import Theorem.Analysis.Section_9_4
/-!
# Analysis I, Section 9.4: Continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuity of functions, using the Mathlib notions

-/


namespace Chapter9

noncomputable abbrev f_9_4_6 (x:ℝ) : ℝ := if x ≥ 0 then 1 else 0

end Chapter9
