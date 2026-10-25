import Mathlib
import Macro.Analysis.Section_11_1
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

theorem BoundedInterval.length_nonneg (I: BoundedInterval) : 0 ≤ |I|ₗ := by
  simp

theorem BoundedInterval.empty_of_lt {I: BoundedInterval} (h: I.b < I.a) : (I:Set ℝ) = ∅ := by
  cases I with
  | Ioo _ _ => simp [le_of_lt h]
  | Icc _ _ => simp [h]
  | Ioc _ _ => simp [le_of_lt h]
  | Ico _ _ => simp [le_of_lt h]

theorem BoundedInterval.dist_le_length {I:BoundedInterval} {x y:ℝ} (hx: x ∈ I) (hy: y ∈ I) : |x - y| ≤ |I|ₗ := by
  apply subset_Icc I at hx; apply subset_Icc I at hy; simp_all [mem_iff, abs_le']; grind

end Chapter11
