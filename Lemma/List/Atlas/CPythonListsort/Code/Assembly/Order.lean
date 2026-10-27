import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.Order.Part4
open CPythonListsort


namespace CPythonListsort

/--
[comparatorEquivalent_iff_incomparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
lemma comparatorEquivalent_iff_incomparable
  {lt : BoolComparator α}
  {a b : α} :
-- imply
  ComparatorEquivalent lt a b ↔ ¬lt a b = true ∧ ¬lt b a = true := by
-- proof
  simp [ComparatorEquivalent]

end CPythonListsort

namespace CPythonListsort

/--
[BoolStrictWeakOrder.comparatorEquivalent_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
lemma BoolStrictWeakOrder.comparatorEquivalent_equivalence
  {lt : BoolComparator α}
-- given
  (h : BoolStrictWeakOrder lt) :
-- imply
  Equivalence (ComparatorEquivalent lt) := by
-- proof
  constructor
  · intro a
    rw [comparatorEquivalent_iff_incomparable]
    exact ⟨h.irrefl a, h.irrefl a⟩
  · intro a b hab
    rw [comparatorEquivalent_iff_incomparable] at hab ⊢
    exact ⟨hab.2, hab.1⟩
  · intro a b c hab hbc
    rw [comparatorEquivalent_iff_incomparable] at hab hbc ⊢
    exact h.incomp_trans a b c hab hbc

end CPythonListsort

namespace CPythonListsort

/--
[sorted_iff_no_later_precedes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
lemma sorted_iff_no_later_precedes
  {lt : BoolComparator α}
  {ys : Array α} :
-- imply
  Sorted lt ys ↔ ∀ i j (hi : i < ys.size) (hj : j < ys.size), i < j → ¬lt ys[j] ys[i] = true := by
-- proof
  simpa [Sorted] using
    (List.pairwise_iff_getElem (l := ys.toList)
      (R := fun earlier later => lt later earlier = false))

end CPythonListsort

namespace CPythonListsort

/--
[BoolStrictWeakOrder.false_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
lemma BoolStrictWeakOrder.false_trans
  {lt : BoolComparator α}
  {a b c : α}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hab : lt b a = false)
  (hbc : lt c b = false) :
-- imply
  lt c a = false := by
-- proof
  apply Bool.eq_false_iff.mpr
  intro hca
  have hab' : ¬lt b a = true := by simp [hab]
  have hbc' : ¬lt c b = true := by simp [hbc]
  by_cases hac : lt a b = true
  · exact hbc' (horder.trans c a b hca hac)
  have hincompAB : ¬lt a b = true ∧ ¬lt b a = true := ⟨hac, hab'⟩
  by_cases hbc : lt b c = true
  · exact hab' (horder.trans b c a hbc hca)
  have hincompBC : ¬lt b c = true ∧ ¬lt c b = true := ⟨hbc, hbc'⟩
  exact (horder.incomp_trans a b c hincompAB hincompBC).2 hca

end CPythonListsort

namespace CPythonListsort

/--
[BoolStrictWeakOrder.strict_of_strict_of_not_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
lemma BoolStrictWeakOrder.strict_of_strict_of_not_reverse
  {lt : BoolComparator α}
  {a b c : α}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hab : lt a b = true)
  (hcb : lt c b = false) :
-- imply
  lt a c = true := by
-- proof
  by_cases hac : lt a c = true
  · exact hac
  by_cases hca : lt c a = true
  · have hcnb : ¬lt c b = true := by simp [hcb]
    exact False.elim (hcnb (horder.trans c a b hca hab))
  have hincompAC : ¬lt a c = true ∧ ¬lt c a = true := ⟨hac, hca⟩
  by_cases hbc : lt b c = true
  · exact horder.trans a b c hab hbc
  have hincompCB : ¬lt c b = true ∧ ¬lt b c = true :=
    ⟨by simp [hcb], hbc⟩
  exact False.elim ((horder.incomp_trans a c b hincompAC hincompCB).1 hab)

end CPythonListsort

namespace CPythonListsort

/--
[BoolStrictWeakOrder.strict_of_not_reverse_of_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
lemma BoolStrictWeakOrder.strict_of_not_reverse_of_strict
  {lt : BoolComparator α}
  {a b c : α}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hba : lt b a = false)
  (hbc : lt b c = true) :
-- imply
  lt a c = true := by
-- proof
  by_cases hac : lt a c = true
  · exact hac
  have hacFalse : lt a c = false := Bool.eq_false_iff.mpr hac
  have hfalse : lt b c = false := horder.false_trans hacFalse hba
  exact False.elim (Bool.noConfusion (hfalse.symm.trans hbc))

end CPythonListsort

namespace CPythonListsort

/--
[TaggedOutput.values_fromInput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
lemma TaggedOutput.values_fromInput
  {xs : Array α} :
-- imply
  (TaggedOutput.fromInput xs).values = xs := by
-- proof
  simp only [TaggedOutput.fromInput, TaggedOutput.values, tagOccurrences, Array.map_map]
  change xs.zipIdx.map Prod.fst = xs
  exact Array.zipIdx_map_fst 0 xs

end CPythonListsort

namespace CPythonListsort

/--
[stable_iff_stableOccurrencePermutation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
lemma stable_iff_stableOccurrencePermutation
  {lt : BoolComparator α}
  {xs : Array α}
  {ys : TaggedOutput α} :
-- imply
  Stable lt xs ys ↔ StableOccurrencePermutation lt (tagOccurrences xs).toList ys.occurrences.toList :=
-- proof
  Iff.rfl

end CPythonListsort

/--
[BoolStrictWeakOrder.occurrenceComparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean)
-/
@[path]
private lemma occurrenceComparator_eq
  {lt : BoolComparator α}
-- given
  (h : BoolStrictWeakOrder lt) :
-- imply
  BoolStrictWeakOrder (occurrenceComparator lt) := by
-- proof
  apply CPythonListsort.BoolStrictWeakOrder.occurrenceComparator h


-- created on 2026-10-23
