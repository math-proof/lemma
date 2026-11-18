module

public import Mathlib
public import Abbrev.Analysis.Section_11_1
public import Abbrev.Analysis.Section_11_1.Part2
public import Instance.Analysis.Section_11_1
@[expose] public section
/-!
# Analysis I, Section 11.1: Partitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Bounded intervals and partitions.
- Length of an interval; the lengths of a partition sum to the length of the interval.

-/


namespace Chapter11

open BoundedInterval

abbrev BoundedInterval.joins (K I J: BoundedInterval) : Prop := (I:Set ℝ) ∩ (J:Set ℝ) = ∅
  ∧ (K:Set ℝ) = (I:Set ℝ) ∪ (J:Set ℝ) ∧ K.length = I.length + J.length

end Chapter11
