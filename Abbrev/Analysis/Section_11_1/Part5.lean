import Mathlib
import Theorem.Analysis.Section_11_1.Part11
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

noncomputable abbrev Partition.add_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals ∪ {∅}
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by aesop)
    intro K ⟨ hK, _ ⟩; simp at hK; obtain rfl | hK := hK
    · simp_all [mem_iff]
    apply (P.exists_unique _ hx).unique <;> grind
  contains L hL := by
    simp at hL; obtain rfl | hL := hL
    · simp [subset_iff]
    exact P.contains _ hL
}

open Classical in
noncomputable abbrev Partition.remove_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals.filter (fun J ↦ (J:Set ℝ).Nonempty)
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by grind [mem_iff, Set.nonempty_of_mem])
    intro K ⟨ hK, _ ⟩; simp at hK
    apply (P.exists_unique _ hx).unique <;> grind
  contains _ _ := P.contains _ (by grind)
}

end Chapter11
