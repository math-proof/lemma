import Mathlib
import Abbrev.Analysis.Section_6_4.Part3
/-!
# Analysis I, Section 6.5: Some standard limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some standard limits, including limits of sequences of the form 1/n^α, x^n, and x^(1/n).

-/


namespace Chapter6

instance Sequence.inst_npow : NPow Sequence where
  npow k a := {
    m := a.m
    seq n := if n ≥ a.m then a n ^ k else 0
    vanish := by grind
  }

end Chapter6
