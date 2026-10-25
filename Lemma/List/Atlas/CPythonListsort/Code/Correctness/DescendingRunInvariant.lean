import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Correctness.DescendingRunInvariant.Part2
open CPythonListsort CPythonListsort.DescendingRunSpec CPythonListsort.DescendingRunSpec.Invariant


namespace CPythonListsort.DescendingRunSpec

/--
[normalize_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
private lemma normalize_length (xs : List α) (tailLength : Nat) :
  (normalize xs tailLength).length = xs.length := by
  simp [normalize]

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[pairwise_insert_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
private lemma pairwise_insert_middle
  {R : α → α → Prop} {pre suf : List α} {x : α}
  (hpair : (pre ++ suf).Pairwise R)
  (hleft : ∀ a ∈ pre, R a x)
  (hright : ∀ b ∈ suf, R x b) :
  (pre ++ [x] ++ suf).Pairwise R := by
  have hparts := List.pairwise_append.mp hpair
  apply List.pairwise_append.mpr
  refine ⟨?_, hparts.2.1, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨hparts.1, List.pairwise_singleton R x, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact hleft a ha
  · intro a ha b hb
    rw [List.mem_append] at ha
    obtain ha | ha := ha
    · exact hparts.2.2 a ha b hb
    · simp only [List.mem_singleton] at ha
      subst a
      exact hright b hb

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[normalize_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma normalize_full
  {xs : List α} :
-- imply
  normalize xs xs.length = xs := by
-- proof
  simp [normalize]

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[stableOccurrencePermutation_append_untouched_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma stableOccurrencePermutation_append_untouched_suffix
  {lt : BoolComparator α}
  {canonicalPrefix outputPrefix suffix : List (Occurrence α)}
-- given
  (hprefix : StableOccurrencePermutation lt canonicalPrefix outputPrefix)
  (hcanonical : (canonicalPrefix ++ suffix).Pairwise (StableRelation lt)) :
-- imply
  StableOccurrencePermutation lt (canonicalPrefix ++ suffix) (outputPrefix ++ suffix) := by
-- proof
  refine ⟨hprefix.1.append_right suffix, ?_⟩
  have hparts := List.pairwise_append.mp hcanonical
  apply List.pairwise_append.mpr
  refine ⟨hprefix.2, hparts.2.1, ?_⟩
  intro a ha b hb
  exact hparts.2.2 a (hprefix.1.mem_iff.mp ha) b hb

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[normalize_append_equivalent_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma normalize_append_equivalent_perm
  {current canonical : List α}
  {x : α}
  {tailLength : Nat}
-- given
  (htail : tailLength ≤ current.length)
  (hperm : (normalize current tailLength).Perm canonical) :
-- imply
  (normalize (current ++ [x]) (tailLength + 1)).Perm (canonical ++ [x]) := by
-- proof
  rw [normalize_append_equivalent current x tailLength htail]
  have hswap :
    ([x] ++ (normalize current tailLength).drop tailLength).Perm
      ((normalize current tailLength).drop tailLength ++ [x]) :=
    List.perm_append_comm
  have hinsert :
    ((normalize current tailLength).take tailLength ++ [x] ++
      (normalize current tailLength).drop tailLength).Perm
      (normalize current tailLength ++ [x]) := by
    have hmove := hswap.append_left
      ((normalize current tailLength).take tailLength)
    simpa only [← List.append_assoc, List.take_append_drop] using hmove
  exact hinsert.trans (hperm.append_right [x])

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[normalize_after_strict_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma normalize_after_strict_perm
  {current canonical : List α}
  {x : α}
  {tailLength : Nat}
-- given
  (hperm : (normalize current tailLength).Perm canonical) :
-- imply
  (normalize (reverseSuffix current tailLength ++ [x]) 1).Perm (canonical ++ [x]) := by
-- proof
  rw [normalize_after_strict]
  have hswap :
    ([x] ++ normalize current tailLength).Perm
      (normalize current tailLength ++ [x]) :=
    List.perm_append_comm
  exact hswap.trans (hperm.append_right [x])

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[strict_reverse_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
private lemma strict_reverse_false
  {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
  {a b : α} (hab : lt a b = true) : lt b a = false := by
  apply Bool.eq_false_iff.mpr
  intro hba
  exact horder.irrefl a (horder.trans a b a hab hba)

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[strict_of_equivalent_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
private lemma strict_of_equivalent_left
  {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
  {a a' b : α} (hequiv : ComparatorEquivalent lt a a')
  (hstrict : lt a' b = true) : lt a b = true := by
  by_contra hnot
  have hab : lt a b = false := Bool.eq_false_iff.mpr hnot
  by_cases hba : lt b a = true
  · have hnotA'A : ¬lt a' a = true := by simp [hequiv.2]
    exact False.elim (hnotA'A (horder.trans a' b a hstrict hba))
  · have hbaFalse : lt b a = false := Bool.eq_false_iff.mpr hba
    have hincompA'A : ¬lt a' a = true ∧ ¬lt a a' = true := by
      simp [hequiv.1, hequiv.2]
    have hincompAB : ¬lt a b = true ∧ ¬lt b a = true := by
      simp [hab, hbaFalse]
    exact (horder.incomp_trans a' a b hincompA'A hincompAB).1 hstrict

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[strict_of_equivalent_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
private lemma strict_of_equivalent_right
  {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
  {a b b' : α} (hstrict : lt a b = true)
  (hequiv : ComparatorEquivalent lt b b') : lt a b' = true := by
  by_contra hnot
  have hab' : lt a b' = false := Bool.eq_false_iff.mpr hnot
  by_cases hb'a : lt b' a = true
  · have hnotB'B : ¬lt b' b = true := by simp [hequiv.2]
    exact False.elim (hnotB'B (horder.trans b' a b hb'a hstrict))
  · have hb'aFalse : lt b' a = false := Bool.eq_false_iff.mpr hb'a
    have hincompAB' : ¬lt a b' = true ∧ ¬lt b' a = true := by
      simp [hab', hb'aFalse]
    have hincompB'B : ¬lt b' b = true ∧ ¬lt b b' = true := by
      simp [hequiv.1, hequiv.2]
    exact (horder.incomp_trans a b' b hincompAB' hincompB'B).1 hstrict

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec.Invariant

/--
[of_equivalent_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma of_equivalent_block
  {lt : BoolComparator α}
  {current : List (Occurrence α)}
-- given
  (hne : current ≠ [])
  (hsorted : current.Pairwise (SortedRelation lt))
  (hstable : current.Pairwise (StableRelation lt))
  (hall : ∀ x ∈ current, ComparatorEquivalent lt x.value (current.getLast hne).value) :
-- imply
  Invariant lt current current current.length := by
-- proof
  refine
    { current_ne := hne
      tail_pos := List.length_pos_of_ne_nil hne
      tail_le := le_rfl
      sorted := by simpa using hsorted
      stable := ⟨by simp, by
        unfold StableRelation at hstable
        simpa only [normalize_full] using hstable⟩
      tail_equiv := ?_
      rest_greater := ?_ }
  · intro x hx
    simpa using hall x (by simpa using hx)
  · intro x hx
    simp at hx

end CPythonListsort.DescendingRunSpec.Invariant

namespace CPythonListsort.DescendingRunSpec.Invariant

/--
[singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma singleton
  {lt : BoolComparator α}
  {x : Occurrence α}
-- given
  (horder : BoolStrictWeakOrder lt) :
-- imply
  Invariant lt [x] [x] 1 := by
-- proof
  refine of_equivalent_block (by simp) (by simp) (by simp) ?_
  intro y hy
  simp only [List.mem_singleton] at hy
  subst y
  exact horder.comparatorEquivalent_equivalence.refl x.value

end CPythonListsort.DescendingRunSpec.Invariant

namespace CPythonListsort.DescendingRunSpec.Invariant

/--
[extend_equivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma extend_equivalent
  {lt : BoolComparator α}
  {canonical current : List (Occurrence α)}
  {tailLength : Nat}
  {x : Occurrence α}
-- given
  (horder : BoolStrictWeakOrder lt)
  (h : Invariant lt canonical current tailLength)
  (hequivalent : ComparatorEquivalent lt x.value (current.getLast h.current_ne).value)
  (horigin : ∀ y ∈ canonical, ComparatorEquivalent lt y.value x.value → y.origin < x.origin) :
-- imply
  Invariant lt (canonical ++ [x]) (current ++ [x]) (tailLength + 1) := by
-- proof
  let normalized := normalize current tailLength
  let pre := normalized.take tailLength
  let suf := normalized.drop tailLength
  have hsplit : pre ++ suf = normalized := by
    change normalized.take tailLength ++ normalized.drop tailLength = normalized
    exact List.take_append_drop tailLength normalized
  have hsortedSplit : (pre ++ suf).Pairwise (SortedRelation lt) := by
    rwa [hsplit]
  have hstableSplit : (pre ++ suf).Pairwise (StableRelation lt) := by
    rwa [hsplit]
  have hequivRel := horder.comparatorEquivalent_equivalence
  have hxRest : ∀ y ∈ suf, lt x.value y.value = true := by
    intro y hy
    exact strict_of_equivalent_left horder hequivalent
      (h.rest_greater y (by simpa [suf] using hy))
  have hsortedNew : (pre ++ [x] ++ suf).Pairwise (SortedRelation lt) := by
    apply pairwise_insert_middle hsortedSplit
    · intro y hy
      have hyEquiv := h.tail_equiv y (by simpa [pre] using hy)
      have hxy : ComparatorEquivalent lt x.value y.value :=
        hequivRel.trans hequivalent (hequivRel.symm hyEquiv)
      exact hxy.1
    · intro y hy
      exact strict_reverse_false horder (hxRest y hy)
  have hstableNew : (pre ++ [x] ++ suf).Pairwise (StableRelation lt) := by
    apply pairwise_insert_middle hstableSplit
    · intro y hy _
      apply horigin y
      · apply h.stable.1.mem_iff.mp
        exact List.mem_of_mem_take (by simpa [pre] using hy)
      · exact hequivRel.trans
        (h.tail_equiv y (by simpa [pre] using hy))
        (hequivRel.symm hequivalent)
    · intro y hy hxy
      have htrue := hxRest y hy
      simp [hxy.1] at htrue
  have hnorm :
    normalize (current ++ [x]) (tailLength + 1) = pre ++ [x] ++ suf := by
    simpa [pre, suf, normalized] using
      normalize_append_equivalent current x tailLength h.tail_le
  have hpreLength : pre.length = tailLength := by
    simp [pre, normalized, h.tail_le]
  have hprefixLength : (pre ++ [x]).length = tailLength + 1 := by
    simp [hpreLength]
  have htake :
    (pre ++ [x] ++ suf).take (tailLength + 1) = pre ++ [x] := by
    rwa [← hprefixLength]
  have hdrop :
    (pre ++ [x] ++ suf).drop (tailLength + 1) = suf := by
    rwa [← hprefixLength]
  refine
    { current_ne := by simp
      tail_pos := by omega
      tail_le := by
        simpa only [List.length_append, List.length_singleton] using
          Nat.add_le_add_right h.tail_le 1
      sorted := ?_
      stable := ?_
      tail_equiv := ?_
      rest_greater := ?_ }
  · rw [hnorm]
    exact hsortedNew
  · constructor
    · exact normalize_append_equivalent_perm current canonical x tailLength
      h.tail_le h.stable.1
    · rw [hnorm]
      exact hstableNew
  · intro y hy
    rw [hnorm, htake] at hy
    rw [List.getLast_append_singleton]
    rw [List.mem_append] at hy
    obtain hy | hy := hy
    · exact hequivRel.trans
      (h.tail_equiv y (by simpa [pre] using hy))
      (hequivRel.symm hequivalent)
    · simp only [List.mem_singleton] at hy
      subst y
      exact hequivRel.refl x.value
  · intro y hy
    rw [hnorm, hdrop] at hy
    rw [List.getLast_append_singleton]
    exact hxRest y hy

end CPythonListsort.DescendingRunSpec.Invariant

namespace CPythonListsort.DescendingRunSpec.Invariant

/--
[extend_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma extend_strict
  {lt : BoolComparator α}
  {canonical current : List (Occurrence α)}
  {tailLength : Nat}
  {x : Occurrence α}
-- given
  (horder : BoolStrictWeakOrder lt)
  (h : Invariant lt canonical current tailLength)
  (hstrict : lt x.value (current.getLast h.current_ne).value = true) :
-- imply
  Invariant lt (canonical ++ [x]) (reverseSuffix current tailLength ++ [x]) 1 := by
-- proof
  let normalized := normalize current tailLength
  have hequivRel := horder.comparatorEquivalent_equivalence
  have hxAll : ∀ y ∈ normalized, lt x.value y.value = true := by
    intro y hy
    have hySplit :
      y ∈ normalized.take tailLength ∨
        y ∈ normalized.drop tailLength := by
      rw [← List.mem_append]
      simpa only [List.take_append_drop] using hy
    obtain hy | hy := hySplit
    · exact strict_of_equivalent_right horder hstrict
      (hequivRel.symm
        (h.tail_equiv y (by simpa [normalized] using hy)))
    · exact horder.trans x.value (current.getLast h.current_ne).value
      y.value hstrict
      (h.rest_greater y (by simpa [normalized] using hy))
  have hnorm :
    normalize (reverseSuffix current tailLength ++ [x]) 1 =
      x :: normalized := by
    simpa [normalized] using normalize_after_strict current x tailLength
  refine
    { current_ne := by simp
      tail_pos := by omega
      tail_le := by simp
      sorted := ?_
      stable := ?_
      tail_equiv := ?_
      rest_greater := ?_ }
  · rw [hnorm]
    apply List.pairwise_cons.mpr
    refine ⟨?_, h.sorted⟩
    intro y hy
    exact strict_reverse_false horder (hxAll y (by simpa [normalized] using hy))
  · constructor
    · exact normalize_after_strict_perm current canonical x tailLength
      h.stable.1
    · rw [hnorm]
      apply List.pairwise_cons.mpr
      refine ⟨?_, h.stable.2⟩
      intro y hy hxy
      have htrue := hxAll y (by simpa [normalized] using hy)
      simp [hxy.1] at htrue
  · intro y hy
    rw [hnorm] at hy
    change y ∈ [x] at hy
    rw [List.mem_singleton] at hy
    subst y
    rw [List.getLast_append_singleton]
    exact hequivRel.refl x.value
  · intro y hy
    rw [hnorm] at hy
    change y ∈ normalized at hy
    rw [List.getLast_append_singleton]
    exact hxAll y (by simpa [normalized] using hy)

end CPythonListsort.DescendingRunSpec.Invariant

namespace CPythonListsort.DescendingRunSpec

/--
[descendingInvariantRegressionOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
private lemma descendingInvariantRegressionOrder :
  BoolStrictWeakOrder descendingInvariantRegressionLt := by
  constructor
  let hstrict : IsStrictOrder Nat
    (fun left right => descendingInvariantRegressionLt left right = true) :=
    { irrefl := by simp [descendingInvariantRegressionLt]
      trans := by
        intro a b c hab hbc
        simp [descendingInvariantRegressionLt] at hab hbc ⊢
        omega }
  exact @IsStrictWeakOrder.mk Nat
    (fun left right => descendingInvariantRegressionLt left right = true)
    hstrict (by
      intro a b c hab hbc
      simp [descendingInvariantRegressionLt] at hab hbc ⊢
      omega)

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[descendingRunInvariant_strict_equivalent_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean)
-/
@[path]
lemma descendingRunInvariant_strict_equivalent_regression
-- imply
  Invariant descendingInvariantRegressionLt [descendingInvariantThree, descendingInvariantTwoOne, descendingInvariantTwoTwo] [descendingInvariantThree, descendingInvariantTwoOne, descendingInvariantTwoTwo] 2 ∧ normalize [descendingInvariantThree, descendingInvariantTwoOne, descendingInvariantTwoTwo] 2 = [descendingInvariantTwoOne, descendingInvariantTwoTwo, descendingInvariantThree] := by
-- proof
  have hseed := Invariant.singleton descendingInvariantRegressionOrder
    descendingInvariantThree
  have hstrict := hseed.extend_strict descendingInvariantRegressionOrder
    descendingInvariantTwoOne (by
      norm_num [descendingInvariantRegressionLt,
        descendingInvariantThree, descendingInvariantTwoOne])
  have hequivalent :
    ComparatorEquivalent descendingInvariantRegressionLt
      descendingInvariantTwoTwo.value
      ((reverseSuffix [descendingInvariantThree] 1 ++
        [descendingInvariantTwoOne]).getLast (by simp)).value := by
    norm_num [ComparatorEquivalent, descendingInvariantRegressionLt,
      reverseSuffix, descendingInvariantThree, descendingInvariantTwoOne,
      descendingInvariantTwoTwo]
  have horigin :
    ∀ y ∈ [descendingInvariantThree, descendingInvariantTwoOne],
      ComparatorEquivalent descendingInvariantRegressionLt y.value
        descendingInvariantTwoTwo.value →
        y.origin < descendingInvariantTwoTwo.origin := by
    intro y hy hequiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    obtain rfl | rfl := hy
    · norm_num [ComparatorEquivalent, descendingInvariantRegressionLt,
      descendingInvariantThree, descendingInvariantTwoTwo] at hequiv
    · norm_num [descendingInvariantTwoOne, descendingInvariantTwoTwo]
  have hextended := hstrict.extend_equivalent
    descendingInvariantRegressionOrder descendingInvariantTwoTwo
    hequivalent horigin
  constructor
  · simpa [reverseSuffix] using hextended
  · norm_num [normalize, descendingInvariantThree,
    descendingInvariantTwoOne, descendingInvariantTwoTwo]

end CPythonListsort.DescendingRunSpec


-- created on 2026-10-23
