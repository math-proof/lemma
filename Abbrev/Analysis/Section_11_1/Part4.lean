import Mathlib
import Theorem.Analysis.Section_11_1.Part10
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

noncomputable abbrev Partition.join {I J K:BoundedInterval} (P: Partition I) (Q: Partition J) (h: K.joins I J) : Partition K
:=
{
  intervals := P.intervals ∪ Q.intervals
  exists_unique x hx := by
    have := congr(x ∈ $(h.1))
    simp [mem_iff, h.2] at hx; obtain hx | hx := hx
    . choose L _ _ using (P.exists_unique _ hx).exists
      apply ExistsUnique.intro L (by grind)
      intro K ⟨hK, hxK⟩; simp at hK; obtain _ | hKQ := hK
      map_tacs [apply (P.exists_unique _ hx).unique; apply (K.subset_iff _).mp (Q.contains _ hKQ) at hxK]
      all_goals grind
    choose L hLQ hxL using (Q.exists_unique _ hx).exists
    apply ExistsUnique.intro L (by grind)
    intro K ⟨hK, hxK⟩; simp at hK; obtain hKP | _ := hK
    map_tacs [apply (K.subset_iff _).mp (P.contains _ hKP) at hxK; apply (Q.exists_unique _ hx).unique]
    all_goals grind
  contains L hL := by
    simp at hL; obtain hLP | hLQ := hL
    . apply Set.Subset.trans ((subset_iff L I).mp (P.contains _ hLP)); simp [h]
    apply Set.Subset.trans ((subset_iff L J).mp (Q.contains _ hLQ)); simp [h]
}

end Chapter11
