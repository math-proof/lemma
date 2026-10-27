import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Correctness.ReverseModeAlgebra.Part4
open CPythonListsort CPythonListsort.ReverseStableOccurrencePermutation CPythonListsort.SortSlice CPythonListsort.ListSortInput


namespace CPythonListsort

/--
[requestedComparator_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma requestedComparator_false
  {lt : BoolComparator α} :
-- imply
  requestedComparator lt false = lt := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[requestedComparator_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma requestedComparator_true
  {lt : BoolComparator α} :
-- imply
  requestedComparator lt true = swappedComparator lt := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceComparator_swapped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma occurrenceComparator_swapped
  {lt : BoolComparator α} :
-- imply
  occurrenceComparator (swappedComparator lt) = swappedComparator (occurrenceComparator lt) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[BoolStrictWeakOrder.swapped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma BoolStrictWeakOrder.swapped
  {lt : BoolComparator α}
-- given
  (h : BoolStrictWeakOrder lt) :
-- imply
  BoolStrictWeakOrder (swappedComparator lt) := by
-- proof
  refine
    { toIsStrictWeakOrder :=
      { toIsStrictOrder :=
        { toIrrefl := ⟨fun value => h.irrefl value⟩
          toIsTrans :=
            ⟨fun first second third hfirstSecond hsecondThird =>
              h.trans third second first hsecondThird hfirstSecond⟩ }
        incomp_trans := ?_ } }
  intro first second third hfirstSecond hsecondThird
  have hfirstSecond' :
    ¬lt first second = true ∧ ¬lt second first = true := by
    simpa [swappedComparator, and_comm] using hfirstSecond
  have hsecondThird' :
    ¬lt second third = true ∧ ¬lt third second = true := by
    simpa [swappedComparator, and_comm] using hsecondThird
  have hfirstThird := h.incomp_trans first second third
    hfirstSecond' hsecondThird'
  simpa [swappedComparator, and_comm] using hfirstThird

end CPythonListsort

namespace CPythonListsort

/--
[Sorted.reverse_swapped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma Sorted.reverse_swapped
  {lt : BoolComparator α}
  {values : Array α}
-- given
  (h : Sorted lt values) :
-- imply
  Sorted (swappedComparator lt) values.reverse := by
-- proof
  rw [Sorted, Array.toList_reverse, List.pairwise_reverse]
  simpa [Sorted, swappedComparator] using h

end CPythonListsort

namespace CPythonListsort

/--
[mirrorOrigin_lt_mirrorOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma mirrorOrigin_lt_mirrorOrigin
  {size earlier later : Nat}
-- given
  (hearlier : earlier < later)
  (hlater : later < size) :
-- imply
  mirrorOrigin size later < mirrorOrigin size earlier := by
-- proof
  rw [mirrorOrigin_of_lt size later hlater,
    mirrorOrigin_of_lt size earlier (hearlier.trans hlater)]
  omega

end CPythonListsort

namespace CPythonListsort

/--
[mirrorOrigin_lt_mirrorOrigin_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma mirrorOrigin_lt_mirrorOrigin_iff
  {size left right : Nat}
-- given
  (hleft : left < size)
  (hright : right < size) :
-- imply
  mirrorOrigin size left < mirrorOrigin size right ↔ right < left := by
-- proof
  rw [mirrorOrigin_of_lt size left hleft,
    mirrorOrigin_of_lt size right hright]
  omega

end CPythonListsort

namespace CPythonListsort

/--
[StableOccurrencePermutation.mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma StableOccurrencePermutation.mirror
  {lt : BoolComparator α}
  {size : Nat}
  {canonical output : List (Occurrence α)}
-- given
  (h : StableOccurrencePermutation lt canonical output)
  (hCanonicalOrigins : ∀ occurrence ∈ canonical, occurrence.origin < size) :
-- imply
  ReverseStableOccurrencePermutation lt (canonical.map (mirrorOccurrence size)) (output.map (mirrorOccurrence size)) := by
-- proof
  constructor
  · exact h.1.map (mirrorOccurrence size)
  · have hmirrored : output.Pairwise fun earlier later =>
    ComparatorEquivalent lt
      (mirrorOccurrence size earlier).value
      (mirrorOccurrence size later).value →
      (mirrorOccurrence size later).origin <
        (mirrorOccurrence size earlier).origin := by
    apply h.2.imp_of_mem
    intro earlier later _ hlater hstable hequivalent
    exact mirrorOrigin_lt_mirrorOrigin (hstable hequivalent)
      (hCanonicalOrigins later (h.1.mem_iff.mp hlater))
    exact hmirrored.map (mirrorOccurrence size) (fun _ _ relation => relation)

end CPythonListsort

namespace CPythonListsort

/--
[Sorted.mirror_reverse_swapped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma Sorted.mirror_reverse_swapped
  {lt : BoolComparator α}
  {size : Nat}
  {entries : Array (Occurrence α)}
-- given
  (h : Sorted (occurrenceComparator lt) entries) :
-- imply
  Sorted (occurrenceComparator (swappedComparator lt)) (entries.map (mirrorOccurrence size)).reverse := by
-- proof
  have hmirrored :
    Sorted (occurrenceComparator lt)
      (entries.map (mirrorOccurrence size)) := by
    rw [Sorted, Array.toList_map]
    exact h.map (mirrorOccurrence size) (by
      intro earlier later hrelation
      exact hrelation)
  simpa only [occurrenceComparator_swapped] using hmirrored.reverse_swapped

end CPythonListsort

namespace CPythonListsort

/--
[sorted_occurrenceComparator_iff_values](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma sorted_occurrenceComparator_iff_values
  {lt : BoolComparator α}
  {entries : Array (Occurrence α)} :
-- imply
  Sorted (occurrenceComparator lt) entries ↔ Sorted lt (entries.map Occurrence.value) := by
-- proof
  unfold Sorted
  rw [Array.toList_map, List.pairwise_map]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[Sorted.values](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma Sorted.values
  {lt : BoolComparator α}
  {entries : Array (Occurrence α)}
-- given
  (h : Sorted (occurrenceComparator lt) entries) :
-- imply
  Sorted lt (entries.map Occurrence.value) :=
-- proof
  (sorted_occurrenceComparator_iff_values lt entries).mp h

end CPythonListsort

namespace CPythonListsort

/--
[Stable.values_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma Stable.values_perm
  {lt : BoolComparator α}
  {xs : Array α}
  {ys : TaggedOutput α}
-- given
  (h : Stable lt xs ys) :
-- imply
  ys.values.toList.Perm xs.toList := by
-- proof
  have htagValues :
    (tagOccurrences xs).toList.map Occurrence.value = xs.toList := by
    simpa [TaggedOutput.fromInput, TaggedOutput.values, Array.toList_map] using
      congrArg Array.toList (TaggedOutput.values_fromInput xs)
  unfold TaggedOutput.values
  rw [Array.toList_map]
  rw [← htagValues]
  exact h.1.map Occurrence.value

end CPythonListsort

namespace CPythonListsort.SortSlice

/--
[reverseEntries_entries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma reverseEntries_entries
  {slice : SortSlice κ ν} :
-- imply
  slice.reverseEntries.entries = slice.entries.reverse := by
-- proof
  rfl

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[reverseEntries_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma reverseEntries_size
  {slice : SortSlice κ ν} :
-- imply
  slice.reverseEntries.entries.size = slice.entries.size := by
-- proof
  simp [reverseEntries]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[reverseEntries_reverseEntries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma reverseEntries_reverseEntries
  {slice : SortSlice κ ν} :
-- imply
  slice.reverseEntries.reverseEntries = slice := by
-- proof
  cases slice
  simp [reverseEntries]

end CPythonListsort.SortSlice

namespace CPythonListsort.ListSortInput

/--
[reverseEntries_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma reverseEntries_slice
  {input : ListSortInput κ ν} :
-- imply
  input.reverseEntries.slice = input.slice.reverseEntries := by
-- proof
  rfl

end CPythonListsort.ListSortInput

namespace CPythonListsort.ListSortInput

/--
[reverseEntries_hasKeyfunc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma reverseEntries_hasKeyfunc
  {input : ListSortInput κ ν} :
-- imply
  input.reverseEntries.hasKeyfunc = input.hasKeyfunc := by
-- proof
  rfl

end CPythonListsort.ListSortInput

namespace CPythonListsort.ListSortInput

/--
[reverseEntries_valuesMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma reverseEntries_valuesMode
  {input : ListSortInput κ ν} :
-- imply
  SortSlice.ValuesModeInvariant input.hasKeyfunc input.reverseEntries.slice :=
-- proof
  input.reverseEntries.valuesMode

end CPythonListsort.ListSortInput

namespace CPythonListsort.ListSortInput

/--
[reverseEntries_reverseEntries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma reverseEntries_reverseEntries
  {input : ListSortInput κ ν} :
-- imply
  input.reverseEntries.reverseEntries = input := by
-- proof
  cases input
  simp [reverseEntries, SortSlice.reverseEntries]

end CPythonListsort.ListSortInput

namespace CPythonListsort

/--
[tagOccurrences_getElem_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma tagOccurrences_getElem_origin
  {xs : Array α}
  {index : Nat}
-- given
  (hindex : index < (tagOccurrences xs).size) :
-- imply
  (tagOccurrences xs)[index].origin = index := by
-- proof
  simp [tagOccurrences]

end CPythonListsort

namespace CPythonListsort

/--
[tagOccurrences_origin_lt_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma tagOccurrences_origin_lt_size
  {xs : Array α}
  {occurrence : Occurrence α}
-- given
  (hoccurrence : occurrence ∈ (tagOccurrences xs).toList) :
-- imply
  occurrence.origin < xs.size := by
-- proof
  rcases List.mem_iff_getElem.mp hoccurrence with
    ⟨index, hindex, hoccurrenceEq⟩
  rw [← hoccurrenceEq]
  simp only [Array.getElem_toList]
  rw [tagOccurrences_getElem_origin]
  simpa [tagOccurrences] using hindex

end CPythonListsort

namespace CPythonListsort

/--
[tagOccurrences_reverse_map_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma tagOccurrences_reverse_map_mirror
  {xs : Array α} :
-- imply
  (tagOccurrences xs.reverse).map (mirrorOccurrence xs.size) = (tagOccurrences xs).reverse := by
-- proof
  apply Array.ext <;>
    simp [tagOccurrences, mirrorOccurrence, mirrorOrigin]
  omega

end CPythonListsort

namespace CPythonListsort

/--
[tagSortSliceOccurrences_reverseEntries_map_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma tagSortSliceOccurrences_reverseEntries_map_mirror
  {source : SortSlice κ ν} :
-- imply
  mirrorSortSlice source.entries.size (tagSortSliceOccurrences source.reverseEntries) = (tagSortSliceOccurrences source).reverseEntries := by
-- proof
  cases source with
  | mk entries =>
    simp only [SortSlice.reverseEntries, tagSortSliceOccurrences,
      mirrorSortSlice]
    congr 1
    apply Array.ext <;>
      simp [mirrorSortSliceEntry, mirrorOccurrence, mirrorOrigin]
    omega

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_reverseEntries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma mirrorSortSlice_reverseEntries
  {size : Nat}
  {slice : SortSlice (Occurrence κ) ν} :
-- imply
  mirrorSortSlice size slice.reverseEntries = (mirrorSortSlice size slice).reverseEntries := by
-- proof
  cases slice with
  | mk entries =>
    simp [mirrorSortSlice, SortSlice.reverseEntries, Array.map_reverse]

end CPythonListsort

namespace CPythonListsort

/--
[ListSortInput.mirror_withOccurrenceKeys_reverseEntries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma ListSortInput.mirror_withOccurrenceKeys_reverseEntries
  {input : ListSortInput κ ν} :
-- imply
  mirrorSortSlice input.slice.entries.size input.reverseEntries.withOccurrenceKeys.slice = input.withOccurrenceKeys.slice.reverseEntries :=
-- proof
tagSortSliceOccurrences_reverseEntries_map_mirror input.slice

end CPythonListsort

namespace CPythonListsort

/--
[EntrySnapshotPermutation.mirror_reversedSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma EntrySnapshotPermutation.mirror_reversedSource
  {source : SortSlice κ ν}
  {current : SortSlice (Occurrence κ) ν}
-- given
  (h : EntrySnapshotPermutation source.reverseEntries current) :
-- imply
  EntrySnapshotPermutation source (mirrorSortSlice source.entries.size current) := by
-- proof
  have hmapped := h.map (mirrorSortSliceEntry source.entries.size)
  have hmapped' :
    (mirrorSortSlice source.entries.size current).entries.toList.Perm
      (mirrorSortSlice source.entries.size
        (tagSortSliceOccurrences source.reverseEntries)).entries.toList := by
    simpa [EntrySnapshotPermutation, mirrorSortSlice,
      Array.toList_map] using hmapped
  rw [tagSortSliceOccurrences_reverseEntries_map_mirror] at hmapped'
  unfold EntrySnapshotPermutation
  exact hmapped'.trans (by
    simp [SortSlice.reverseEntries])

end CPythonListsort

namespace CPythonListsort

/--
[stable_reversedSource_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma stable_reversedSource_mirror
  {lt : BoolComparator α}
  {xs : Array α}
  {output : List (Occurrence α)}
-- given
  (h : StableOccurrencePermutation lt (tagOccurrences xs.reverse).toList output) :
-- imply
  ReverseStableOccurrencePermutation lt (tagOccurrences xs).toList (output.map (mirrorOccurrence xs.size)) := by
-- proof
  have hOrigins :
    ∀ occurrence ∈ (tagOccurrences xs.reverse).toList,
      occurrence.origin < xs.size := by
    intro occurrence hoccurrence
    simpa using tagOccurrences_origin_lt_size hoccurrence
  have hmirrored := h.mirror hOrigins
  have hCanonical :
    (tagOccurrences xs.reverse).toList.map (mirrorOccurrence xs.size) =
      (tagOccurrences xs).toList.reverse := by
    simpa [Array.toList_map] using
      congrArg Array.toList (tagOccurrences_reverse_map_mirror xs)
  constructor
  · have hperm := hmirrored.1
    rw [hCanonical] at hperm
    exact hperm.trans (tagOccurrences xs).toList.reverse_perm
  · exact hmirrored.2

end CPythonListsort

namespace CPythonListsort

/--
[stable_reversedSource_mirror_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma stable_reversedSource_mirror_reverse
  {lt : BoolComparator α}
  {xs : Array α}
  {output : List (Occurrence α)}
-- given
  (h : StableOccurrencePermutation lt (tagOccurrences xs.reverse).toList output) :
-- imply
  StableOccurrencePermutation (swappedComparator lt) (tagOccurrences xs).toList (output.map (mirrorOccurrence xs.size)).reverse :=
-- proof
(stable_reversedSource_mirror h).reverse

end CPythonListsort

namespace CPythonListsort

/--
[StableOccurrencePermutation.mirror_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
lemma StableOccurrencePermutation.mirror_reverse
  {lt : BoolComparator α}
  {size : Nat}
  {canonical output canonicalFinal : List (Occurrence α)}
-- given
  (h : StableOccurrencePermutation lt canonical output)
  (hCanonicalOrigins : ∀ occurrence ∈ canonical, occurrence.origin < size)
  (hCanonicalFinal : (canonical.map (mirrorOccurrence size)).reverse = canonicalFinal) :
-- imply
  StableOccurrencePermutation (swappedComparator lt) canonicalFinal ((output.map (mirrorOccurrence size)).reverse) := by
-- proof
  constructor
  · have hmap := h.1.map (mirrorOccurrence size)
    have hreverseOutput :=
      List.reverse_perm (output.map (mirrorOccurrence size))
    have hreverseCanonical :=
      (List.reverse_perm (canonical.map (mirrorOccurrence size))).symm
    rw [← hCanonicalFinal]
    exact hreverseOutput.trans (hmap.trans hreverseCanonical)
  · rw [List.pairwise_reverse]
    have hmirrored : output.Pairwise fun earlier later =>
      ComparatorEquivalent (swappedComparator lt)
        (mirrorOccurrence size later).value
        (mirrorOccurrence size earlier).value →
        (mirrorOccurrence size later).origin <
          (mirrorOccurrence size earlier).origin := by
      apply h.2.imp_of_mem
      intro earlier later hearlier hlater hstable hequivalent
      rw [comparatorEquivalent_swapped] at hequivalent
      have hequivalent' :
        ComparatorEquivalent lt earlier.value later.value :=
        ⟨hequivalent.2, hequivalent.1⟩
      have horigin : earlier.origin < later.origin := hstable hequivalent'
      exact mirrorOrigin_lt_mirrorOrigin horigin
        (hCanonicalOrigins later (h.1.mem_iff.mp hlater))
    exact hmirrored.map (mirrorOccurrence size) (fun _ _ relation => relation)

end CPythonListsort

/--
[BoolStrictWeakOrder.requestedComparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
private lemma requestedComparator_eq
  {lt : BoolComparator α}
  {reverse : Bool}
-- given
  (h : BoolStrictWeakOrder lt) :
-- imply
  BoolStrictWeakOrder (requestedComparator lt reverse) := by
-- proof
  apply CPythonListsort.BoolStrictWeakOrder.requestedComparator h reverse

/--
[comparatorEquivalent_swapped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
private lemma comparatorEquivalent_swapped_eq
  {lt : BoolComparator α}
  {left right : α} :
-- imply
  ComparatorEquivalent (swappedComparator lt) left right ↔ ComparatorEquivalent lt left right := by
-- proof
  apply CPythonListsort.comparatorEquivalent_swapped lt left right

/--
[reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
private lemma reverse_eq
  {lt : BoolComparator α}
  {canonical output : List (Occurrence α)}
-- given
  (h : ReverseStableOccurrencePermutation lt canonical output) :
-- imply
  StableOccurrencePermutation (swappedComparator lt) canonical output.reverse := by
-- proof
  apply CPythonListsort.ReverseStableOccurrencePermutation.reverse h

/--
[ValuesModeInvariant.reverseEntries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean)
-/
@[path]
private lemma reverseEntries_eq
  {hasKeyfunc : Bool}
  {slice : SortSlice κ ν}
-- given
  (h : ValuesModeInvariant hasKeyfunc slice) :
-- imply
  ValuesModeInvariant hasKeyfunc slice.reverseEntries := by
-- proof
  apply CPythonListsort.SortSlice.ValuesModeInvariant.reverseEntries h


-- created on 2026-10-23
