import Mathlib
import Theorem.Analysis.Section_5_5.Part5
import Theorem.Analysis.Section_5_epilogue.Part5
import Theorem.Analysis.Section_6_2
open EReal

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals {name}`EReal`, particularly with regard to the supremum
  operation {name}`sSup` and infimum operation {name}`sInf`.

-/


abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

