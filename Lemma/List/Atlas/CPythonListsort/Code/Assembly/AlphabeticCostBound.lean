import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.AlphabeticCostBound.Part2
open CPythonListsort CPythonListsort.MergeTree CPythonListsort.MergePlan


namespace CPythonListsort


/--
[runLengths_ofLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma runLengths_ofLengths
  {first : Nat}
  {rest : List Nat} :
-- imply
  (ofLengths first rest).runLengths = first :: rest := by
-- proof
  induction rest generalizing first with
  | nil => rfl
  | cons second rest ih =>
    simp [ofLengths, MergeTree.runLengths, ih]
namespace MergePlan


namespace CPythonListsort

/--
[weightedBinaryEntropy_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma weightedBinaryEntropy_append
  {total : Nat}
  {left right : List Nat} :
-- imply
  weightedBinaryEntropy total (left ++ right) = weightedBinaryEntropy total left + weightedBinaryEntropy total right := by
-- proof
  simp [weightedBinaryEntropy]

end CPythonListsort

namespace CPythonListsort

/--
[binaryEntropyTerm_add_complement_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
private lemma binaryEntropyTerm_add_complement_le_one
  (p : Real) :
  binaryEntropyTerm p + binaryEntropyTerm (1 - p) ≤ 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound := Real.binEntropy_le_log_two (p := p)
  have heq :
    binaryEntropyTerm p + binaryEntropyTerm (1 - p) =
      Real.binEntropy p / Real.log 2 := by
    simp only [binaryEntropyTerm, Real.logb, Real.binEntropy]
    ring
  rw [heq]
  exact (div_le_iff₀ hlog).2 (by simpa using hbound)

end CPythonListsort

namespace CPythonListsort

/--
[weightedBinaryEntropy_change_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma weightedBinaryEntropy_change_total
  {lengths : List Nat}
  {oldTotal newTotal : Nat}
-- given
  (hold : 0 < oldTotal)
  (hnew : 0 < newTotal)
  (hpositive : ∀ length ∈ lengths, 0 < length) :
-- imply
  weightedBinaryEntropy newTotal lengths = weightedBinaryEntropy oldTotal lengths + (lengths.sum : Real) * Real.logb 2 ((newTotal : Real) / (oldTotal : Real)) := by
-- proof
  induction lengths with
  | nil => simp [weightedBinaryEntropy]
  | cons length rest ih =>
    have hlength : 0 < length := hpositive length (by simp)
    have hrest : ∀ candidate ∈ rest, 0 < candidate := by
      intro candidate hcandidate
      exact hpositive candidate (by simp [hcandidate])
    change
      (length : Real) *
        Real.logb 2 ((newTotal : Real) / (length : Real)) +
        weightedBinaryEntropy newTotal rest =
        (length : Real) *
          Real.logb 2 ((oldTotal : Real) / (length : Real)) +
          weightedBinaryEntropy oldTotal rest +
            ((length + rest.sum : Nat) : Real) *
              Real.logb 2 ((newTotal : Real) / (oldTotal : Real))
    rw [ih hrest]
    have holdReal : (oldTotal : Real) ≠ 0 := by positivity
    have hnewReal : (newTotal : Real) ≠ 0 := by positivity
    have hlengthReal : (length : Real) ≠ 0 := by positivity
    have hfactor :
      (newTotal : Real) / (length : Real) =
        ((newTotal : Real) / (oldTotal : Real)) *
          ((oldTotal : Real) / (length : Real)) := by
      field_simp
    rw [hfactor, Real.logb_mul]
    · push_cast
      ring
    · exact div_ne_zero hnewReal holdReal
    · exact div_ne_zero holdReal hlengthReal

end CPythonListsort

namespace CPythonListsort

/--
[weightedBinaryEntropy_binary_split_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma weightedBinaryEntropy_binary_split_le
  {leftTotal rightTotal : Nat}
-- given
  (hleft : 0 < leftTotal)
  (hright : 0 < rightTotal) :
-- imply
  (leftTotal : Real) * Real.logb 2 (((leftTotal + rightTotal : Nat) : Real) / (leftTotal : Real)) + (rightTotal : Real) * Real.logb 2 (((leftTotal + rightTotal : Nat) : Real) / (rightTotal : Real)) ≤ (leftTotal + rightTotal : Nat) := by
-- proof
  let total : Real := (leftTotal + rightTotal : Nat)
  let p : Real := (leftTotal : Real) / total
  have htotal : 0 < total := by
    dsimp [total]
    positivity
  have htotalNe : total ≠ 0 := htotal.ne'
  have hleftReal : (leftTotal : Real) ≠ 0 := by positivity
  have hrightReal : (rightTotal : Real) ≠ 0 := by positivity
  have hpInv : p⁻¹ = total / (leftTotal : Real) := by
    dsimp [p]
    field_simp
  have hcomp : 1 - p = (rightTotal : Real) / total := by
    dsimp [p, total]
    push_cast
    field_simp
    ring
  have hcompInv : (1 - p)⁻¹ = total / (rightTotal : Real) := by
    rw [hcomp]
    field_simp
  have hscaled :
    (leftTotal : Real) *
      Real.logb 2 (total / (leftTotal : Real)) +
      (rightTotal : Real) *
        Real.logb 2 (total / (rightTotal : Real)) =
      total *
        (binaryEntropyTerm p + binaryEntropyTerm (1 - p)) := by
    rw [binaryEntropyTerm, binaryEntropyTerm, hpInv, hcompInv, hcomp]
    dsimp [p]
    field_simp
  change
    (leftTotal : Real) *
      Real.logb 2 (total / (leftTotal : Real)) +
      (rightTotal : Real) *
        Real.logb 2 (total / (rightTotal : Real)) ≤ total
  rw [hscaled]
  nlinarith [binaryEntropyTerm_add_complement_le_one p]

end CPythonListsort

namespace CPythonListsort

/--
[totalLength_pos_of_runLengths_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lower bound for its merge cost.  Alphabeticity is built into leaf order but
is not otherwise needed for this information-theoretic inequality. -/
private lemma MergeTree.totalLength_pos_of_runLengths_positive
  (tree : MergeTree)
  (hpositive : ∀ length ∈ tree.runLengths, 0 < length) :
  0 < tree.totalLength := by
  induction tree with
  | leaf length =>
    simpa [MergeTree.runLengths, MergeTree.totalLength] using
      hpositive length (by simp [MergeTree.runLengths])
  | merge power left right ihLeft ihRight =>
    have hleft : ∀ length ∈ left.runLengths, 0 < length := by
      intro length hlength
      exact hpositive length (by simp [MergeTree.runLengths, hlength])
    have hright : ∀ length ∈ right.runLengths, 0 < length := by
      intro length hlength
      exact hpositive length (by simp [MergeTree.runLengths, hlength])
    have hleftTotal := ihLeft hleft
    have hrightTotal := ihRight hright
    simp only [MergeTree.totalLength]
    omega

end CPythonListsort

namespace CPythonListsort

/--
[MergeTree.weightedBinaryEntropy_le_mergeCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma MergeTree.weightedBinaryEntropy_le_mergeCost
  {tree : MergeTree}
-- given
  (hpositive : ∀ length ∈ tree.runLengths, 0 < length) :
-- imply
  weightedBinaryEntropy tree.totalLength tree.runLengths ≤ (tree.mergeCost : Real) := by
-- proof
  induction tree with
  | leaf length =>
    have hlength : 0 < length := hpositive length (by simp [MergeTree.runLengths])
    simp [weightedBinaryEntropy, MergeTree.runLengths,
      MergeTree.totalLength, MergeTree.mergeCost, hlength.ne']
  | merge power left right ihLeft ihRight =>
    have hleftPositive : ∀ length ∈ left.runLengths, 0 < length := by
      intro length hlength
      exact hpositive length (by simp [MergeTree.runLengths, hlength])
    have hrightPositive : ∀ length ∈ right.runLengths, 0 < length := by
      intro length hlength
      exact hpositive length (by simp [MergeTree.runLengths, hlength])
    have hleftTotal : 0 < left.totalLength := by
      exact left.totalLength_pos_of_runLengths_positive hleftPositive
    have hrightTotal : 0 < right.totalLength := by
      exact right.totalLength_pos_of_runLengths_positive hrightPositive
    have hleftShift := weightedBinaryEntropy_change_total
      left.runLengths left.totalLength
      (left.totalLength + right.totalLength)
      hleftTotal (by omega) hleftPositive
    have hrightShift := weightedBinaryEntropy_change_total
      right.runLengths right.totalLength
      (left.totalLength + right.totalLength)
      hrightTotal (by omega) hrightPositive
    have hsplit := weightedBinaryEntropy_binary_split_le
      left.totalLength right.totalLength hleftTotal hrightTotal
    simp only [MergeTree.runLengths, MergeTree.totalLength,
      MergeTree.mergeCost, weightedBinaryEntropy_append]
    rw [hleftShift, hrightShift]
    rw [left.sum_runLengths, right.sum_runLengths]
    push_cast at hsplit ⊢
    nlinarith [ihLeft hleftPositive, ihRight hrightPositive]

end CPythonListsort

namespace CPythonListsort

/--
[RunProfile.entropy_mul_le_mergeCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma RunProfile.entropy_mul_le_mergeCost
  {n : Nat}
  {profile : RunProfile n}
  {tree : MergeTree}
-- given
  (hlengths : tree.runLengths = profile.lengths) :
-- imply
  (n : Real) * profile.entropy ≤ (tree.mergeCost : Real) := by
-- proof
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have htreePositive : ∀ length ∈ tree.runLengths, 0 < length := by
      intro length hlength
      exact profile.positive length (by simpa [hlengths] using hlength)
    have htotal : tree.totalLength = n := by
      rw [← tree.sum_runLengths, hlengths, profile.sum_eq]
    have hscaled :
      (n : Real) * profile.entropy =
        weightedBinaryEntropy n profile.lengths := by
      unfold RunProfile.entropy RunProfile.fractions binaryEntropy
      simp only [List.map_map]
      rw [← List.sum_map_mul_left]
      unfold weightedBinaryEntropy
      apply congrArg List.sum
      apply List.map_congr_left
      intro length hlength
      have hlengthPos := profile.positive length hlength
      have hnReal : (n : Real) ≠ 0 := by positivity
      simp only [Function.comp_apply, binaryEntropyTerm]
      rw [inv_div]
      field_simp
    rw [hscaled, ← hlengths, ← htotal]
    exact tree.weightedBinaryEntropy_le_mergeCost htreePositive

end CPythonListsort

namespace CPythonListsort.MergeTree

/--
[optimalAlphabeticMergeCost_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma optimalAlphabeticMergeCost_spec
  {lengths : List Nat} :
-- imply
  HasAlphabeticMergeCost lengths (optimalAlphabeticMergeCost lengths) := by
-- proof
  classical
  exact Nat.find_spec (exists_alphabeticMergeCost lengths)

end CPythonListsort

namespace CPythonListsort

/--
[optimalAlphabeticMergeCost_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma optimalAlphabeticMergeCost_le
  {lengths : List Nat}
  {plan : MergePlan}
-- given
  (hlengths : plan.runLengths = lengths) :
-- imply
  optimalAlphabeticMergeCost lengths ≤ plan.mergeCost := by
-- proof
  classical
  apply Nat.find_min' (exists_alphabeticMergeCost lengths)
  exact ⟨plan, hlengths, rfl⟩

end CPythonListsort

namespace CPythonListsort

/--
[optimalAlphabeticMergeCost_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma optimalAlphabeticMergeCost_nil
-- imply
  optimalAlphabeticMergeCost [] = 0 := by
-- proof
  apply Nat.eq_zero_of_le_zero
  simpa [MergePlan.runLengths, MergePlan.mergeCost] using
    optimalAlphabeticMergeCost_le [] MergePlan.empty rfl

end CPythonListsort

namespace CPythonListsort

/--
[optimalAlphabeticMergeCost_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma optimalAlphabeticMergeCost_singleton
  {length : Nat} :
-- imply
  optimalAlphabeticMergeCost [length] = 0 := by
-- proof
  apply Nat.eq_zero_of_le_zero
  simpa [MergePlan.runLengths, MergePlan.mergeCost, MergeTree.runLengths,
    MergeTree.mergeCost] using
    optimalAlphabeticMergeCost_le [length]
      (.tree (.leaf length)) rfl

end CPythonListsort

namespace CPythonListsort

/--
[RunProfile.entropy_mul_le_planMergeCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma RunProfile.entropy_mul_le_planMergeCost
  {n : Nat}
  {profile : RunProfile n}
  {plan : MergePlan}
-- given
  (hlengths : plan.runLengths = profile.lengths) :
-- imply
  (n : Real) * profile.entropy ≤ (plan.mergeCost : Real) := by
-- proof
  cases plan with
  | empty =>
    have hnil : profile.lengths = [] := by
      simpa [MergePlan.runLengths] using hlengths.symm
    have hn : n = 0 := by
      rw [← profile.sum_eq, hnil]
      simp
    subst n
    simp
  | tree root =>
    exact profile.entropy_mul_le_mergeCost root
      (by simpa [MergePlan.runLengths] using hlengths)

end CPythonListsort

namespace CPythonListsort

/--
[RunProfile.entropy_mul_le_optimalAlphabeticMergeCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma RunProfile.entropy_mul_le_optimalAlphabeticMergeCost
  {n : Nat}
  {profile : RunProfile n} :
-- imply
  (n : Real) * profile.entropy ≤ (optimalAlphabeticMergeCost profile.lengths : Real) := by
-- proof
  rcases optimalAlphabeticMergeCost_spec profile.lengths with
    ⟨plan, hlengths, hcost⟩
  rw [← hcost]
  exact profile.entropy_mul_le_planMergeCost plan hlengths

end CPythonListsort

namespace CPythonListsort

/--
[mergeCost_le_any_alphabetic_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma mergeCost_le_any_alphabetic_add_two
  {n implementationCost : Nat}
  {profile : RunProfile n}
  {tree : MergeTree}
-- given
  (himplementation : (implementationCost : Real) ≤ (n : Real) * profile.entropy + 2 * (n : Real))
  (hlengths : tree.runLengths = profile.lengths) :
-- imply
  (implementationCost : Real) ≤ (tree.mergeCost : Real) + 2 * (n : Real) := by
-- proof
  have hlower := profile.entropy_mul_le_mergeCost tree hlengths
  nlinarith

end CPythonListsort

namespace CPythonListsort

/--
[mergeCost_le_optimalAlphabetic_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
lemma mergeCost_le_optimalAlphabetic_add_two
  {n implementationCost : Nat}
  {profile : RunProfile n}
-- given
  (himplementation : (implementationCost : Real) ≤ (n : Real) * profile.entropy + 2 * (n : Real)) :
-- imply
  (implementationCost : Real) ≤ (optimalAlphabeticMergeCost profile.lengths : Real) + 2 * (n : Real) := by
-- proof
  have hlower := profile.entropy_mul_le_optimalAlphabeticMergeCost
  nlinarith

end CPythonListsort

/--
[runLengths_ofLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
private lemma runLengths_ofLengths_eq_2
  {lengths : List Nat} :
-- imply
  (ofLengths lengths).runLengths = lengths := by
-- proof
  apply CPythonListsort.MergePlan.runLengths_ofLengths lengths

/--
[exists_alphabeticMergeCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean)
-/
@[path]
private lemma exists_alphabeticMergeCost_eq
  {lengths : List Nat} :
-- imply
  ∃ cost, HasAlphabeticMergeCost lengths cost := by
-- proof
  apply CPythonListsort.exists_alphabeticMergeCost lengths


-- created on 2026-10-23
