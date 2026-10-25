import Mathlib
import Theorem.Analysis.Section_8_1.Part4
import Theorem.Analysis.Section_8_2.Part4
import Theorem.Analysis.Section_8_3
/-!
# Analysis I, Section 8.3: Uncountable sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Uncountable sets.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

-/


namespace Chapter8

abbrev LeCard (X Y: Type) : Prop := ∃ f: X → Y, Function.Injective f

abbrev LtCard (X Y: Type) : Prop := LeCard X Y ∧ ¬ EqualCard X Y

end Chapter8
