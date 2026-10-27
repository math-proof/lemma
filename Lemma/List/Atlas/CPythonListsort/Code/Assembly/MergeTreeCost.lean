import Mathlib
import Initialize.Tactic.Attr.Basic
import Inductive.CPythonListsort.Code.Assembly.MergeTreeCost
open CPythonListsort CPythonListsort.SpannedMergeTree
open-subtree lengths `[148, 36, 32, 32, 8]`. Paper top-pair completion totals


namespace CPythonListsort.SpannedMergeTree

/--
[leaf_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma leaf_valid
  {span : RunSpan} :
-- imply
  (leaf span).Valid := by
-- proof
  simp [Valid, leaf, MergeTree.totalLength]

end CPythonListsort.SpannedMergeTree

namespace CPythonListsort.SpannedMergeTree

/--
[merge_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma merge_valid
  {power : Nat}
  {left right : SpannedMergeTree}
-- given
  (hleft : left.Valid)
  (hright : right.Valid) :
-- imply
  (merge power left right).Valid := by
-- proof
  simp only [Valid] at hleft hright ⊢
  simp only [merge, MergeTree.totalLength, RunSpan.merge]
  omega

end CPythonListsort.SpannedMergeTree

namespace CPythonListsort

/--
[topPairCompletionCost_cons_of_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
private lemma topPairCompletionCost_cons_of_ne_nil
  (first : Nat) {rest : List Nat} (hrest : rest ≠ []) :
  topPairCompletionCost (first :: rest) =
    first + rest.sum + topPairCompletionCost rest := by
  cases rest with
  | nil => contradiction
  | cons second tail => rfl

end CPythonListsort

namespace CPythonListsort

/--
[topPairCompletionCost_prefix_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
suffixes of equal total length, including an already-paid local merge cost. -/
private lemma topPairCompletionCost_prefix_add_le
  (before : List Nat) {left right : List Nat} (extra : Nat)
  (hleft : left ≠ []) (hright : right ≠ [])
  (hsum : left.sum = right.sum)
  (hcost : extra + topPairCompletionCost left ≤
    topPairCompletionCost right) :
  extra + topPairCompletionCost (before ++ left) ≤
    topPairCompletionCost (before ++ right) := by
  induction before with
  | nil => simpa using hcost
  | cons first before ih =>
    have hbeforeLeft : before ++ left ≠ [] := by simp [hleft]
    have hbeforeRight : before ++ right ≠ [] := by simp [hright]
    change
      extra + topPairCompletionCost (first :: (before ++ left)) ≤
        topPairCompletionCost (first :: (before ++ right))
    rw [topPairCompletionCost_cons_of_ne_nil first hbeforeLeft,
      topPairCompletionCost_cons_of_ne_nil first hbeforeRight]
    have ih' := ih
    simp only [List.sum_append, hsum] at ih' ⊢
    omega

end CPythonListsort

namespace CPythonListsort

/--
[topPairCompletionCost_merge_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma topPairCompletionCost_merge_top
  {before : List Nat}
  {left right : Nat} :
-- imply
  left + right + topPairCompletionCost (before ++ [left + right]) = topPairCompletionCost (before ++ [left, right]) := by
-- proof
  induction before with
  | nil => simp [topPairCompletionCost]
  | cons first before ih =>
    have hmerged : before ++ [left + right] ≠ [] := by simp
    have hpair : before ++ [left, right] ≠ [] := by simp
    change
      left + right +
        topPairCompletionCost (first :: (before ++ [left + right])) =
        topPairCompletionCost (first :: (before ++ [left, right]))
    rw [topPairCompletionCost_cons_of_ne_nil first hmerged,
      topPairCompletionCost_cons_of_ne_nil first hpair]
    simp only [List.sum_append, List.sum_cons, List.sum_nil]
    omega

end CPythonListsort

namespace CPythonListsort

/--
[topPairCompletionCost_merge_thirdLast_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma topPairCompletionCost_merge_thirdLast_le
  {before : List Nat}
  {a b c : Nat}
-- given
  (hselect : a < c) :
-- imply
  a + b + topPairCompletionCost (before ++ [a + b, c]) ≤ topPairCompletionCost (before ++ [a, b, c]) := by
-- proof
  apply topPairCompletionCost_prefix_add_le before (extra := a + b)
  · simp
  · simp
  · simp
    omega
  · simp [topPairCompletionCost]
    omega

end CPythonListsort

namespace CPythonListsort

/--
[CPythonForceCollapseCost.cost_eq_zero_of_length_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma CPythonForceCollapseCost.cost_eq_zero_of_length_le_one
  {lengths : List Nat}
  {cost : Nat}
-- given
  (hcollapse : CPythonForceCollapseCost lengths cost)
  (hlength : lengths.length ≤ 1) :
-- imply
  cost = 0 := by
-- proof
  induction hcollapse with
  | empty => rfl
  | singleton => rfl
  | pair left right => simp at hlength
  | mergeTop before a b c tailCost hselect tail ih =>
    simp at hlength
  | mergeThirdLast before a b c tailCost hselect tail ih =>
    simp at hlength

end CPythonListsort

namespace CPythonListsort

/--
[CPythonForceCollapseCost.empty_cost_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma CPythonForceCollapseCost.empty_cost_eq_zero
  {cost : Nat}
-- given
  (hcollapse : CPythonForceCollapseCost [] cost) :
-- imply
  cost = 0 :=
-- proof
  hcollapse.cost_eq_zero_of_length_le_one (by simp)

end CPythonListsort

namespace CPythonListsort

/--
[CPythonForceCollapseCost.singleton_cost_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma CPythonForceCollapseCost.singleton_cost_eq_zero
  {length cost : Nat}
-- given
  (hcollapse : CPythonForceCollapseCost [length] cost) :
-- imply
  cost = 0 :=
-- proof
  hcollapse.cost_eq_zero_of_length_le_one (by simp)

end CPythonListsort

namespace CPythonListsort

/--
[CPythonForceCollapseCost.le_topPairCompletionCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma CPythonForceCollapseCost.le_topPairCompletionCost
  {lengths : List Nat}
  {cost : Nat}
-- given
  (hcollapse : CPythonForceCollapseCost lengths cost) :
-- imply
  cost ≤ topPairCompletionCost lengths := by
-- proof
  induction hcollapse with
  | empty => simp [topPairCompletionCost]
  | singleton length => simp [topPairCompletionCost]
  | pair left right => simp [topPairCompletionCost]
  | mergeTop before a b c tailCost hselect tail ih =>
    calc
      b + c + tailCost ≤
        b + c + topPairCompletionCost (before ++ [a, b + c]) := by
          omega
      _ = topPairCompletionCost (before ++ [a, b, c]) := by
        simpa [List.append_assoc] using
          topPairCompletionCost_merge_top (before ++ [a]) b c
  | mergeThirdLast before a b c tailCost hselect tail ih =>
    calc
      a + b + tailCost ≤
        a + b + topPairCompletionCost (before ++ [a + b, c]) := by
          omega
      _ ≤ topPairCompletionCost (before ++ [a, b, c]) :=
        topPairCompletionCost_merge_thirdLast_le before a b c hselect

end CPythonListsort

namespace CPythonListsort

/--
[cpythonForceCollapseCost_le_topPairCompletionCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma cpythonForceCollapseCost_le_topPairCompletionCost
  {lengths : List Nat}
  {cost : Nat}
-- given
  (_hpositive : PositiveRunLengths lengths)
  (hcollapse : CPythonForceCollapseCost lengths cost) :
-- imply
  cost ≤ topPairCompletionCost lengths :=
-- proof
  hcollapse.le_topPairCompletionCost

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapse_rotation_cost_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
lemma forceCollapse_rotation_cost_regression
-- imply
  topPairCompletionCost [148, 36, 32, 32, 8] = 476 ∧ CPythonForceCollapseCost [148, 36, 32, 32, 8] 472 ∧ 213 + 476 = 689 ∧ 213 + 472 = 685 := by
-- proof
  refine ⟨by norm_num [topPairCompletionCost], ?_, by norm_num, by norm_num⟩
  apply CPythonForceCollapseCost.mergeTop [148, 36] 32 32 8 432
  · norm_num
  apply CPythonForceCollapseCost.mergeThirdLast [148] 36 32 40 364
  · norm_num
  apply CPythonForceCollapseCost.mergeTop [] 148 68 40 256
  · norm_num
  exact CPythonForceCollapseCost.pair 148 108

end CPythonListsort

/--
[topPairCompletionMergeCosts_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean)
-/
@[path]
private lemma topPairCompletionMergeCosts_sum_eq :
-- imply
  ∀ lengths : List Nat, (topPairCompletionMergeCosts lengths).sum = topPairCompletionCost lengths := by
-- proof
  apply CPythonListsort.topPairCompletionMergeCosts_sum


-- created on 2026-10-23
