import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.MergeCost
open CPythonListsort CPythonListsort.RunProfile CPythonListsort.MergeTree CPythonListsort.MergePlan


namespace CPythonListsort.RunProfile

/--
[lengths_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma lengths_eq_nil
  {profile : RunProfile 0} :
-- imply
  profile.lengths = [] := by
-- proof
  cases hlengths : profile.lengths with
  | nil => rfl
  | cons length rest =>
    have hpositive : 0 < length := profile.positive length (by simp [hlengths])
    have hsum : length + rest.sum = 0 := by
      simpa [hlengths] using profile.sum_eq
    omega

end CPythonListsort.RunProfile

namespace CPythonListsort.RunProfile

/--
[lengths_eq_nil_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma lengths_eq_nil_iff
  {profile : RunProfile n} :
-- imply
  profile.lengths = [] ↔ n = 0 := by
-- proof
  constructor
  · intro hlengths
    rw [← profile.sum_eq, hlengths]
    simp
  · intro hn
    subst n
    exact profile.lengths_eq_nil

end CPythonListsort.RunProfile

namespace CPythonListsort

/--
[binaryEntropy_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma binaryEntropy_nil
-- imply
  binaryEntropy [] = 0 := by
-- proof
  simp [binaryEntropy]

end CPythonListsort

namespace CPythonListsort

/--
[RunProfile.entropy_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma RunProfile.entropy_zero
  {profile : RunProfile 0} :
-- imply
  profile.entropy = 0 := by
-- proof
  rw [RunProfile.entropy, RunProfile.fractions, profile.lengths_eq_nil]
  simp

end CPythonListsort

namespace CPythonListsort.MergeTree

/--
[mergeCost_eq_weightedPathLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma mergeCost_eq_weightedPathLength
  {tree : MergeTree} :
-- imply
  tree.mergeCost = tree.weightedPathLength := by
-- proof
  simpa [weightedPathLength] using (tree.weightedPathLengthAt_eq 0).symm

end CPythonListsort.MergeTree

namespace CPythonListsort.MergePlan

/--
[leavesWithDepth_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma leavesWithDepth_fst
  {depth : Nat} :
-- imply
  ∀ tree : MergeTree, (tree.leavesWithDepth depth).map Prod.fst = tree.runLengths := by
-- proof
  cases plan with
  | empty => simp [leavesWithDepth, runLengths]
  | tree root => simp [leavesWithDepth, runLengths]

end CPythonListsort.MergePlan

namespace CPythonListsort.MergePlan

/--
[mergeCost_eq_weightedPathLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma mergeCost_eq_weightedPathLength
  {plan : MergePlan} :
-- imply
  plan.mergeCost = plan.weightedPathLength := by
-- proof
  cases plan with
  | empty => rfl
  | tree root => exact root.mergeCost_eq_weightedPathLength

end CPythonListsort.MergePlan

namespace CPythonListsort

/--
[RunProfile.sum_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma RunProfile.sum_cast
  {profile : RunProfile n} :
-- imply
  (List.map (fun length : Nat => (length : ℝ)) profile.lengths).sum = (n : ℝ) := by
-- proof
  rw [← Nat.cast_list_sum, profile.sum_eq]

end CPythonListsort

namespace CPythonListsort

/--
[RunProfile.fractions_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma RunProfile.fractions_sum
  {profile : RunProfile n}
-- given
  (hn : 0 < n) :
-- imply
  profile.fractions.sum = 1 := by
-- proof
  rw [RunProfile.fractions]
  simp only [div_eq_mul_inv]
  rw [List.sum_map_mul_right, profile.sum_cast]
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  exact mul_inv_cancel₀ hnreal

end CPythonListsort

namespace CPythonListsort

/--
[weightedDepthTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
private lemma weightedDepthTerm_le
  {n length depth : Nat} (hn : 0 < n)
  (hdepth :
    (depth : ℝ) ≤
      Real.logb 2 ((n : ℝ) / (length : ℝ)) + 2) :
  ((length * depth : Nat) : ℝ) ≤
    (n : ℝ) * binaryEntropyTerm ((length : ℝ) / (n : ℝ)) +
      2 * (length : ℝ) := by
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  have hscale :
    (n : ℝ) * ((length : ℝ) / (n : ℝ)) = (length : ℝ) := by
    field_simp
  have hdepth' :
    (depth : ℝ) ≤
      Real.logb 2 (((length : ℝ) / (n : ℝ))⁻¹) + 2 := by
    simpa only [inv_div] using hdepth
  have hmul := mul_le_mul_of_nonneg_left hdepth' (Nat.cast_nonneg length)
  simp only [Nat.cast_mul, binaryEntropyTerm]
  rw [← mul_assoc, hscale]
  nlinarith

end CPythonListsort

namespace CPythonListsort

/--
[weightedPathLength_le_entropy_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma weightedPathLength_le_entropy_add_two
  {n : Nat}
  {profile : RunProfile n}
  {leaves : List (Nat × Nat)}
-- given
  (hlengths : leaves.map Prod.fst = profile.lengths)
  (hdepth : ∀ leaf ∈ leaves, (leaf.2 : ℝ) ≤ Real.logb 2 ((n : ℝ) / (leaf.1 : ℝ)) + 2) :
-- imply
  (((leaves.map fun leaf => leaf.1 * leaf.2).sum : Nat) : ℝ) ≤ (n : ℝ) * profile.entropy + 2 * (n : ℝ) := by
-- proof
  by_cases hnzero : n = 0
  · subst n
    have hprofile : profile.lengths = [] := profile.lengths_eq_nil
    have hleaves : leaves = [] := by
      exact List.eq_nil_of_map_eq_nil (hlengths.trans hprofile)
    subst leaves
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hnzero
    rw [Nat.cast_list_sum]
    calc
      (List.map (↑) (leaves.map fun leaf => leaf.1 * leaf.2)).sum ≤
        (leaves.map fun leaf =>
          (n : ℝ) * binaryEntropyTerm ((leaf.1 : ℝ) / (n : ℝ)) +
            2 * (leaf.1 : ℝ)).sum := by
        rw [List.map_map]
        apply List.sum_le_sum
        intro leaf hleaf
        simpa [Function.comp_apply] using
          weightedDepthTerm_le hn (hdepth leaf hleaf)
      _ = (n : ℝ) * profile.entropy + 2 * (n : ℝ) := by
        rw [List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left]
        have hfractions :
          List.map (fun leaf => (leaf.1 : ℝ) / (n : ℝ)) leaves =
            profile.fractions := by
          calc
            List.map (fun leaf => (leaf.1 : ℝ) / (n : ℝ)) leaves =
              List.map (fun length : Nat => (length : ℝ) / (n : ℝ))
                (List.map Prod.fst leaves) := by
              simp only [List.map_map, Function.comp_def]
            _ = List.map (fun length : Nat => (length : ℝ) / (n : ℝ))
              profile.lengths := by
              rw [hlengths]
            _ = profile.fractions := rfl
        have hcastLengths :
          (List.map (fun leaf => (leaf.1 : ℝ)) leaves).sum = (n : ℝ) := by
          calc
            (List.map (fun leaf => (leaf.1 : ℝ)) leaves).sum =
              (List.map (fun length : Nat => (length : ℝ))
                (List.map Prod.fst leaves)).sum := by
              simp only [List.map_map, Function.comp_def]
            _ = (List.map (fun length : Nat => (length : ℝ))
              profile.lengths).sum := by
              rw [hlengths]
            _ = (n : ℝ) := profile.sum_cast
        have hentropy :
          (List.map (fun leaf =>
            binaryEntropyTerm ((leaf.1 : ℝ) / (n : ℝ))) leaves).sum =
              profile.entropy := by
          calc
            (List.map (fun leaf =>
              binaryEntropyTerm ((leaf.1 : ℝ) / (n : ℝ))) leaves).sum =
              binaryEntropy
                (List.map (fun leaf => (leaf.1 : ℝ) / (n : ℝ)) leaves) := by
              simp only [binaryEntropy, List.map_map, Function.comp_def]
            _ = binaryEntropy profile.fractions := congrArg binaryEntropy hfractions
            _ = profile.entropy := rfl
        rw [hentropy, hcastLengths]

end CPythonListsort

namespace CPythonListsort

/--
[MergePlan.mergeCost_le_entropy_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma MergePlan.mergeCost_le_entropy_add_two
  {n : Nat}
  {plan : MergePlan}
  {profile : RunProfile n}
-- given
  (hlengths : plan.runLengths = profile.lengths)
  (hdepth : ∀ leaf ∈ plan.leavesWithDepth, (leaf.2 : ℝ) ≤ Real.logb 2 ((n : ℝ) / (leaf.1 : ℝ)) + 2) :
-- imply
  (plan.mergeCost : ℝ) ≤ (n : ℝ) * profile.entropy + 2 * (n : ℝ) := by
-- proof
  rw [plan.mergeCost_eq_weightedPathLength]
  cases plan with
  | empty =>
    simpa only [MergePlan.weightedPathLength, List.map_nil, List.sum_nil,
      Nat.cast_zero] using
      weightedPathLength_le_entropy_add_two profile []
        (by simpa [MergePlan.runLengths] using hlengths) (by simp)
  | tree root =>
    simpa only [MergePlan.weightedPathLength, MergeTree.weightedPathLength,
      MergeTree.weightedPathLengthAt] using
        weightedPathLength_le_entropy_add_two profile (root.leavesWithDepth 0)
          (by simpa [MergePlan.runLengths] using hlengths) hdepth

end CPythonListsort

namespace CPythonListsort

/--
[MergePlan.mergeCost_le_entropy_mul_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
lemma MergePlan.mergeCost_le_entropy_mul_add_two
  {n : Nat}
  {plan : MergePlan}
  {profile : RunProfile n}
-- given
  (hlengths : plan.runLengths = profile.lengths)
  (hdepth : ∀ leaf ∈ plan.leavesWithDepth, (leaf.2 : ℝ) ≤ Real.logb 2 ((n : ℝ) / (leaf.1 : ℝ)) + 2) :
-- imply
  (plan.mergeCost : ℝ) ≤ profile.entropy * (n : ℝ) + 2 * (n : ℝ) := by
-- proof
  simpa only [mul_comm] using
    plan.mergeCost_le_entropy_add_two profile hlengths hdepth

end CPythonListsort

/--
[sum_runLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
private lemma sum_runLengths_eq :
-- imply
  ∀ tree : MergeTree, tree.runLengths.sum = tree.totalLength := by
-- proof
  apply CPythonListsort.MergeTree.sum_runLengths

/--
[weightedPathLengthAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
private lemma weightedPathLengthAt_eq_eq
  {depth : Nat} :
-- imply
  ∀ tree : MergeTree, tree.weightedPathLengthAt depth = tree.mergeCost + depth * tree.totalLength := by
-- proof
  apply CPythonListsort.MergeTree.weightedPathLengthAt_eq depth

/--
[leavesWithDepth_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean)
-/
@[path]
private lemma leavesWithDepth_fst_eq_2
  {plan : MergePlan} :
-- imply
  plan.leavesWithDepth.map Prod.fst = plan.runLengths := by
-- proof
  apply CPythonListsort.MergePlan.leavesWithDepth_fst plan


-- created on 2026-10-23
