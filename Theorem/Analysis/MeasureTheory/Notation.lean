import Mathlib
import Abbrev.Analysis.MeasureTheory.Notation


theorem Set.indicator'_apply {X: Type*} (E: Set X) (x: X) [Decidable (x ∈ E)] : indicator' E x = if x ∈ E then 1 else 0 := indicator_apply _ _ _

theorem Set.indicator'_of_mem {X: Type*} {E:Set X} {x:X} (h: x ∈ E) : indicator' E x = 1 :=
  indicator_of_mem h _

theorem Set.indicator'_of_notMem {X: Type*} {E:Set X} {x:X} (h: x ∉ E) : indicator' E x = 0 :=
  indicator_of_notMem h _

