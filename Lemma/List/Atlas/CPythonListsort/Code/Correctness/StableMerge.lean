import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Correctness.StableMerge
open CPythonListsort


namespace CPythonListsort

/--
[stableOccurrenceLE_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableOccurrenceLE_eq_true
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : Occurrence alpha} :
-- imply
  stableOccurrenceLE lt left right = true ↔ lt right.value left.value = false := by
-- proof
  simp [stableOccurrenceLE]

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryLE_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryLE_eq_true
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  stableEntryLE lt left right = true ↔ lt right.key.value left.key.value = false := by
-- proof
  simp [stableEntryLE]

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_keys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_keys
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : List (SortSliceEntry (Occurrence alpha) nu)} :
-- imply
  (stableEntryMerge lt left right).map SortSliceEntry.key = stableOccurrenceMerge lt (left.map SortSliceEntry.key) (right.map SortSliceEntry.key) := by
-- proof
  unfold stableEntryMerge stableOccurrenceMerge
  apply List.map_merge
  intro a _ b _
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_perm_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_perm_append
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : List (SortSliceEntry (Occurrence alpha) nu)} :
-- imply
  (stableEntryMerge lt left right).Perm (left ++ right) :=
-- proof
List.merge_perm_append (stableEntryLE lt)

end CPythonListsort

namespace CPythonListsort

/--
[stableOccurrenceMerge_perm_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableOccurrenceMerge_perm_append
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : List (Occurrence alpha)} :
-- imply
  (stableOccurrenceMerge lt left right).Perm (left ++ right) :=
-- proof
List.merge_perm_append (stableOccurrenceLE lt)

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[stableOccurrenceLE_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
private lemma stableOccurrenceLE_trans
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
  (a b c : Occurrence alpha)
  (hab : stableOccurrenceLE lt a b = true)
  (hbc : stableOccurrenceLE lt b c = true) :
  stableOccurrenceLE lt a c = true := by
  rw [stableOccurrenceLE_eq_true] at hab hbc ⊢
  exact horder.false_trans hab hbc
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[stableOccurrenceLE_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
private lemma stableOccurrenceLE_total
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
  (a b : Occurrence alpha) :
  stableOccurrenceLE lt a b || stableOccurrenceLE lt b a := by
  simp only [stableOccurrenceLE]
  cases hab : lt b.value a.value <;> cases hba : lt a.value b.value <;>
    simp_all
  exact False.elim (horder.irrefl a.value
    (horder.trans a.value b.value a.value hba hab))

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[sortedRelation_pairwise_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
private lemma sortedRelation_pairwise_merge
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
  (left right : List (Occurrence alpha))
  (hleft : left.Pairwise (DescendingRunSpec.SortedRelation lt))
  (hright : right.Pairwise (DescendingRunSpec.SortedRelation lt)) :
  (stableOccurrenceMerge lt left right).Pairwise
    (DescendingRunSpec.SortedRelation lt) := by
  have hleft' : left.Pairwise
    (fun a b => stableOccurrenceLE lt a b = true) := by
    change left.Pairwise (fun a b => lt b.value a.value = false) at hleft
    simpa using hleft
  have hright' : right.Pairwise
    (fun a b => stableOccurrenceLE lt a b = true) := by
    change right.Pairwise (fun a b => lt b.value a.value = false) at hright
    simpa using hright
  have hmerged := List.pairwise_merge
    (stableOccurrenceLE_trans horder)
    (stableOccurrenceLE_total horder) left right hleft' hright'
  change (stableOccurrenceMerge lt left right).Pairwise
    (fun a b => lt b.value a.value = false)
  simpa [stableOccurrenceMerge] using hmerged

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[pairwise_stable_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
private lemma pairwise_stable_merge
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt) :
  ∀ (left right : List (Occurrence alpha)),
    left.Pairwise (DescendingRunSpec.SortedRelation lt) →
    right.Pairwise (DescendingRunSpec.SortedRelation lt) →
    (left ++ right).Pairwise (DescendingRunSpec.StableRelation lt) →
    (stableOccurrenceMerge lt left right).Pairwise
      (DescendingRunSpec.StableRelation lt)
  | [], right, _, _, hstable => by
    simpa [stableOccurrenceMerge] using hstable
  | left, [], _, _, hstable => by
    simpa [stableOccurrenceMerge] using hstable
  | a :: left, b :: right, hleftSorted, hrightSorted, hstable => by
    rw [stableOccurrenceMerge, List.cons_merge_cons]
    by_cases hchoose : stableOccurrenceLE lt a b = true
    · rw [if_pos hchoose]
      apply List.Pairwise.cons
      · intro x hx
        rw [List.mem_merge] at hx
        have hparts := List.pairwise_append.mp hstable
        rcases hx with hx | hx
        · exact List.rel_of_pairwise_cons hparts.1 hx
        · exact hparts.2.2 a (by simp) x hx
      · have hparts :=
  List.pairwise_append.mp hstable
    apply pairwise_stable_merge horder left (b :: right)
    · exact hleftSorted.tail
    · exact hrightSorted
    · apply List.pairwise_append.mpr
      exact ⟨hparts.1.tail, hparts.2.1,
        fun x hx y hy => hparts.2.2 x (by simp [hx]) y hy⟩
    · rw [if_neg hchoose]
      apply List.Pairwise.cons
      · intro x hx
        rw [List.mem_merge] at hx
        have hparts := List.pairwise_append.mp hstable
        obtain hx | hx := hx
        · intro hequiv
          have hba : lt b.value a.value = true := by
            simpa [stableOccurrenceLE] using hchoose
          have hxa : lt x.value a.value = false := by
            simp only [List.mem_cons] at hx
            obtain hxa | hx := hx
            · subst x
              exact Bool.eq_false_iff.mpr (horder.irrefl a.value)
            · exact List.rel_of_pairwise_cons hleftSorted hx
          have hbx := horder.strict_of_strict_of_not_reverse hba hxa
          exact Bool.noConfusion (hequiv.1.symm.trans hbx)
        · exact List.rel_of_pairwise_cons hparts.2.1 hx
      · have hparts := List.pairwise_append.mp hstable
        apply pairwise_stable_merge horder (a :: left) right
        · exact hleftSorted
        · exact hrightSorted.tail
        · apply List.pairwise_append.mpr
          exact ⟨hparts.1, hparts.2.1.tail,
            fun x hx y hy => hparts.2.2 x hx y (by simp [hy])⟩
termination_by left right => left.length + right.length

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_append_right_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_append_right_block
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {suffix : List (SortSliceEntry (Occurrence alpha) nu)} :
-- imply
  ∀ (left right : List (SortSliceEntry (Occurrence alpha) nu)), (∀ leftEntry ∈ left, ∀ suffixEntry ∈ suffix, lt suffixEntry.key.value leftEntry.key.value = false) → stableEntryMerge lt left (right ++ suffix) = stableEntryMerge lt left right ++ suffix :=
-- proof
  hafter leftHead (by simp) suffixHead (by simp)
  have htail :
    ∀ leftEntry ∈ left,
      ∀ suffixEntry ∈ suffixHead :: suffixTail,
        lt suffixEntry.key.value leftEntry.key.value = false := by
    intro leftEntry hleft suffixEntry hsuffix
    exact hafter leftEntry (by simp [hleft]) suffixEntry hsuffix
  simp only [List.nil_append]
  unfold stableEntryMerge
  rw [List.cons_merge_cons]
  have hchoose : stableEntryLE lt leftHead suffixHead = true := by
    simp [stableEntryLE, stableOccurrenceLE, hnotStrict]
  rw [if_pos hchoose]
  have ih := stableEntryMerge_append_right_block lt
    (suffixHead :: suffixTail) left [] htail
  simpa [stableEntryMerge] using congrArg (List.cons leftHead) ih
  | leftHead :: left, rightHead :: right, hafter => by
    have hleft :
      ∀ leftEntry ∈ left, ∀ suffixEntry ∈ suffix,
        lt suffixEntry.key.value leftEntry.key.value = false := by
      intro leftEntry hmem suffixEntry hsuffix
      exact hafter leftEntry (by simp [hmem]) suffixEntry hsuffix
    have hright :
      ∀ leftEntry ∈ leftHead :: left, ∀ suffixEntry ∈ suffix,
        lt suffixEntry.key.value leftEntry.key.value = false := hafter
    simp only [List.cons_append]
    unfold stableEntryMerge
    rw [List.cons_merge_cons, List.cons_merge_cons]
    by_cases hchoose : stableEntryLE lt leftHead rightHead = true
    · simp only [hchoose, ↓reduceIte, List.cons_append]
      have ih := stableEntryMerge_append_right_block lt suffix left
        (rightHead :: right) hleft
      simpa [stableEntryMerge] using congrArg (List.cons leftHead) ih
    · simp only [hchoose]
      have ih := stableEntryMerge_append_right_block lt suffix
        (leftHead :: left) right hright
      simpa [stableEntryMerge] using congrArg (List.cons rightHead) ih
termination_by left right => left.length + right.length

end CPythonListsort

namespace CPythonListsort

/--
[stableOccurrenceMerge_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableOccurrenceMerge_correct
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {canonical left right : List (Occurrence alpha)}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hleft : left.Pairwise (DescendingRunSpec.SortedRelation lt))
  (hright : right.Pairwise (DescendingRunSpec.SortedRelation lt))
  (hstable : StableOccurrencePermutation lt canonical (left ++ right)) :
-- imply
  (stableOccurrenceMerge lt left right).Pairwise (DescendingRunSpec.SortedRelation lt) ∧ StableOccurrencePermutation lt canonical (stableOccurrenceMerge lt left right) := by
-- proof
  refine ⟨sortedRelation_pairwise_merge horder left right hleft hright, ?_⟩
  refine ⟨(stableOccurrenceMerge_perm_append lt left right).trans hstable.1, ?_⟩
  exact pairwise_stable_merge horder left right hleft hright hstable.2

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_correct
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {canonical : List (Occurrence alpha)}
  {left right : List (SortSliceEntry (Occurrence alpha) nu)}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hleft : (left.map SortSliceEntry.key).Pairwise (DescendingRunSpec.SortedRelation lt))
  (hright : (right.map SortSliceEntry.key).Pairwise (DescendingRunSpec.SortedRelation lt))
  (hstable : StableOccurrencePermutation lt canonical (left.map SortSliceEntry.key ++ right.map SortSliceEntry.key)) :
-- imply
  ((stableEntryMerge lt left right).map SortSliceEntry.key).Pairwise (DescendingRunSpec.SortedRelation lt) ∧ StableOccurrencePermutation lt canonical ((stableEntryMerge lt left right).map SortSliceEntry.key) ∧ (stableEntryMerge lt left right).Perm (left ++ right) := by
-- proof
  rw [stableEntryMerge_keys]
  rcases stableOccurrenceMerge_correct horder canonical
    (left.map SortSliceEntry.key) (right.map SortSliceEntry.key)
    hleft hright hstable with ⟨hsorted, hstableOut⟩
  exact ⟨hsorted, hstableOut, stableEntryMerge_perm_append lt left right⟩

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_append_left_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_append_left_block
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {suffix : List (SortSliceEntry (Occurrence alpha) nu)} :
-- imply
  ∀ (left right : List (SortSliceEntry (Occurrence alpha) nu)), (∀ rightEntry ∈ right, ∀ suffixEntry ∈ suffix, lt rightEntry.key.value suffixEntry.key.value = true) → stableEntryMerge lt (left ++ suffix) right = stableEntryMerge lt left right ++ suffix :=
-- proof
  hafter rightHead (by simp) suffixHead (by simp)
  have htail :
    ∀ rightEntry ∈ right,
      ∀ suffixEntry ∈ suffixHead :: suffixTail,
        lt rightEntry.key.value suffixEntry.key.value = true := by
    intro rightEntry hright suffixEntry hsuffix
    exact hafter rightEntry (by simp [hright]) suffixEntry hsuffix
  simp only [List.nil_append]
  unfold stableEntryMerge
  rw [List.cons_merge_cons]
  have hnot :
    ¬stableEntryLE lt suffixHead rightHead = true := by
    simp [stableEntryLE, stableOccurrenceLE, hstrict]
  rw [if_neg hnot]
  have ih := stableEntryMerge_append_left_block lt
    (suffixHead :: suffixTail) [] right htail
  simpa [stableEntryMerge] using congrArg (List.cons rightHead) ih
  | leftHead :: left, [], _ => by simp [stableEntryMerge]
  | leftHead :: left, rightHead :: right, hafter => by
    have hleft :
      ∀ rightEntry ∈ rightHead :: right, ∀ suffixEntry ∈ suffix,
        lt rightEntry.key.value suffixEntry.key.value = true := hafter
    have hright :
      ∀ rightEntry ∈ right, ∀ suffixEntry ∈ suffix,
        lt rightEntry.key.value suffixEntry.key.value = true := by
      intro rightEntry hmem suffixEntry hsuffix
      exact hafter rightEntry (by simp [hmem]) suffixEntry hsuffix
    simp only [List.cons_append]
    unfold stableEntryMerge
    rw [List.cons_merge_cons, List.cons_merge_cons]
    by_cases hchoose : stableEntryLE lt leftHead rightHead = true
    · simp only [hchoose, ↓reduceIte, List.cons_append]
      have ih := stableEntryMerge_append_left_block lt suffix left
        (rightHead :: right) hleft
      simpa [stableEntryMerge] using congrArg (List.cons leftHead) ih
    · simp only [hchoose]
      have ih := stableEntryMerge_append_left_block lt suffix
        (leftHead :: left) right hright
      simpa [stableEntryMerge] using congrArg (List.cons rightHead) ih
termination_by left right => left.length + right.length

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_snoc_left_of_all_right_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_snoc_left_of_all_right_lt
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : List (SortSliceEntry (Occurrence alpha) nu)}
  {lastLeft : SortSliceEntry (Occurrence alpha) nu}
-- given
  (hafter : ∀ rightEntry ∈ right, lt rightEntry.key.value lastLeft.key.value = true) :
-- imply
  stableEntryMerge lt (left ++ [lastLeft]) right = stableEntryMerge lt left right ++ [lastLeft] := by
-- proof
  apply stableEntryMerge_append_left_block lt [lastLeft] left right
  intro rightEntry hright suffixEntry hsuffix
  simp only [List.mem_singleton] at hsuffix
  subst suffixEntry
  exact hafter rightEntry hright

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_snoc_right_of_all_not_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_snoc_right_of_all_not_lt
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : List (SortSliceEntry (Occurrence alpha) nu)}
  {lastRight : SortSliceEntry (Occurrence alpha) nu}
-- given
  (hafter : ∀ leftEntry ∈ left, lt lastRight.key.value leftEntry.key.value = false) :
-- imply
  stableEntryMerge lt left (right ++ [lastRight]) = stableEntryMerge lt left right ++ [lastRight] := by
-- proof
  apply stableEntryMerge_append_right_block lt [lastRight] left right
  intro leftEntry hleft suffixEntry hsuffix
  simp only [List.mem_singleton] at hsuffix
  subst suffixEntry
  exact hafter leftEntry hleft

end CPythonListsort

namespace CPythonListsort

/--
[all_right_lt_suffix_of_pairwise_of_last_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma all_right_lt_suffix_of_pairwise_of_last_lt
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {right suffix : List (SortSliceEntry (Occurrence alpha) nu)}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hrightNe : right ≠ [])
  (hright : right.Pairwise (fun earlier later => lt later.key.value earlier.key.value = false))
  (hboundary : ∀ suffixEntry ∈ suffix, lt (right.getLast hrightNe).key.value suffixEntry.key.value = true) :
-- imply
  ∀ rightEntry ∈ right, ∀ suffixEntry ∈ suffix, lt rightEntry.key.value suffixEntry.key.value = true := by
-- proof
  intro rightEntry hrightMem suffixEntry hsuffix
  have hlastNotBefore :
    lt (right.getLast hrightNe).key.value rightEntry.key.value = false := by
    apply hright.rel_getLast_of_rel_getLast_getLast hrightMem
    exact Bool.eq_false_iff.mpr
      (horder.irrefl (right.getLast hrightNe).key.value)
  exact horder.strict_of_not_reverse_of_strict hlastNotBefore
    (hboundary suffixEntry hsuffix)

end CPythonListsort

namespace CPythonListsort

/--
[all_suffix_not_lt_left_of_pairwise_of_not_lt_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma all_suffix_not_lt_left_of_pairwise_of_not_lt_last
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left suffix : List (SortSliceEntry (Occurrence alpha) nu)}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hleftNe : left ≠ [])
  (hleft : left.Pairwise (fun earlier later => lt later.key.value earlier.key.value = false))
  (hboundary : ∀ suffixEntry ∈ suffix, lt suffixEntry.key.value (left.getLast hleftNe).key.value = false) :
-- imply
  ∀ leftEntry ∈ left, ∀ suffixEntry ∈ suffix, lt suffixEntry.key.value leftEntry.key.value = false := by
-- proof
  intro leftEntry hleftMem suffixEntry hsuffix
  have hlastNotBefore :
    lt (left.getLast hleftNe).key.value leftEntry.key.value = false := by
    apply hleft.rel_getLast_of_rel_getLast_getLast hleftMem
    exact Bool.eq_false_iff.mpr
      (horder.irrefl (left.getLast hleftNe).key.value)
  apply Bool.eq_false_iff.mpr
  intro hsuffixLeft
  have hsuffixLast := horder.strict_of_strict_of_not_reverse hsuffixLeft
    hlastNotBefore
  have hnot :
    ¬lt suffixEntry.key.value (left.getLast hleftNe).key.value = true := by
    simp [hboundary suffixEntry hsuffix]
  exact hnot hsuffixLast

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_equivalent_unequal_left_first_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_equivalent_unequal_left_first_regression
  {alpha : Type u}
  {nu : Type v} :
-- imply
  stableMergeLeftEquivalentEntry.key.value ≠ stableMergeRightEquivalentEntry.key.value ∧ ComparatorEquivalent decadeLt stableMergeLeftEquivalentEntry.key.value stableMergeRightEquivalentEntry.key.value ∧ stableEntryMerge decadeLt [stableMergeLeftEquivalentEntry] [stableMergeRightEquivalentEntry] = [stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry] := by
-- proof
  constructor
  · decide
  constructor
  · norm_num [ComparatorEquivalent, decadeLt,
    stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry]
  · simp [stableEntryMerge, stableEntryLE, stableOccurrenceLE, decadeLt,
    stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry]

end CPythonListsort

namespace CPythonListsort

/--
[stableEntryMerge_strict_right_first_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean)
-/
@[path]
lemma stableEntryMerge_strict_right_first_regression
  {alpha : Type u}
  {nu : Type v} :
-- imply
  stableEntryMerge decadeLt [stableMergeLargerEntry] [stableMergeSmallerEntry] = [stableMergeSmallerEntry, stableMergeLargerEntry] := by
-- proof
  simp [stableEntryMerge, stableEntryLE, stableOccurrenceLE, decadeLt,
    stableMergeLargerEntry, stableMergeSmallerEntry]

end CPythonListsort


-- created on 2026-10-23
