import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Correctness.DescendingRunNormalization
open CPythonListsort CPythonListsort.DescendingRunSpec


namespace CPythonListsort.DescendingRunSpec

/--
[normalize_eq_reverse_reverseSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunNormalization.lean)
-/
@[path]
lemma normalize_eq_reverse_reverseSuffix
  {xs : List α}
  {tailLength : Nat} :
-- imply
  normalize xs tailLength = (reverseSuffix xs tailLength).reverse := by
-- proof
  simp [normalize, reverseSuffix, List.reverse_append]

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[normalize_take_eq_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunNormalization.lean)
-/
@[path]
lemma normalize_take_eq_suffix
  {xs : List α}
  {tailLength : Nat}
-- given
  (htail : tailLength ≤ xs.length) :
-- imply
  (normalize xs tailLength).take tailLength = xs.drop (xs.length - tailLength) := by
-- proof
  have hlength :
    (xs.drop (xs.length - tailLength)).length = tailLength := by
    simp
    omega
  simp [normalize, hlength]

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[normalize_drop_eq_reverse_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunNormalization.lean)
-/
@[path]
lemma normalize_drop_eq_reverse_prefix
  {xs : List α}
  {tailLength : Nat}
-- given
  (htail : tailLength ≤ xs.length) :
-- imply
  (normalize xs tailLength).drop tailLength = (xs.take (xs.length - tailLength)).reverse := by
-- proof
  have hlength :
    (xs.drop (xs.length - tailLength)).length = tailLength := by
    simp
    omega
  simp [normalize, hlength]

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[normalize_append_equivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunNormalization.lean)
-/
@[path]
lemma normalize_append_equivalent
  {xs : List α}
  {x : α}
  {tailLength : Nat}
-- given
  (htail : tailLength ≤ xs.length) :
-- imply
  normalize (xs ++ [x]) (tailLength + 1) = (normalize xs tailLength).take tailLength ++ [x] ++ (normalize xs tailLength).drop tailLength := by
-- proof
  rw [normalize_take_eq_suffix xs tailLength htail,
    normalize_drop_eq_reverse_prefix xs tailLength htail]
  simp only [normalize, List.length_append, List.length_singleton]
  have hsub : xs.length + 1 - (tailLength + 1) =
    xs.length - tailLength := by
    omega
  rw [hsub]
  rw [List.drop_append_of_le_length
    (by omega : xs.length - tailLength ≤ xs.length)]
  rw [List.take_append_of_le_length
    (by omega : xs.length - tailLength ≤ xs.length)]

end CPythonListsort.DescendingRunSpec

namespace CPythonListsort.DescendingRunSpec

/--
[normalize_after_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunNormalization.lean)
-/
@[path]
lemma normalize_after_strict
  {xs : List α}
  {x : α}
  {tailLength : Nat} :
-- imply
  normalize (reverseSuffix xs tailLength ++ [x]) 1 = x :: normalize xs tailLength := by
-- proof
  have hlength : (reverseSuffix xs tailLength).length = xs.length := by
    simp [reverseSuffix]
  simp only [normalize, List.length_append, List.length_singleton, hlength]
  have hsub : xs.length + 1 - 1 = xs.length := by
    omega
  rw [hsub]
  rw [List.drop_append_of_le_length (by simp [hlength])]
  rw [List.take_append_of_le_length (by simp [hlength])]
  have hdrop : (reverseSuffix xs tailLength).drop xs.length = [] := by
    rw [← hlength]
    simp
  have htake :
    (reverseSuffix xs tailLength).take xs.length =
      reverseSuffix xs tailLength := by
    rw [← hlength]
    simp
  rw [hdrop, htake]
  simp [reverseSuffix, List.reverse_append]

end CPythonListsort.DescendingRunSpec


-- created on 2026-10-23
