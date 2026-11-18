module

public import Mathlib
public import Instance.Analysis.Section_11_1.Part3
public import Theorem.Analysis.Section_11_1.Part4

public section
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

@[simp]
public theorem BoundedInterval.mem_inter (I J: BoundedInterval) (x:ℝ) :
  x ∈ (I ∩ J : BoundedInterval) ↔ x ∈ I ∧ x ∈ J := by
  simp [mem_iff]
  change x ∈ ((BoundedInterval.inter I J).choose : Set ℝ) ↔
    x ∈ (I : Set ℝ) ∧ x ∈ (J : Set ℝ)
  rw [← (BoundedInterval.inter I J).choose_spec]
  rfl

end Chapter11
