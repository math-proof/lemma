/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Reversal.lean -/


import Mathlib.Tactic.FinCases
import Def.NumberTheory.MultipleZeta.Reversal.Part2
import Lemma.Nat.MultipleZeta.Reversal
import Def.MathlibExtTest.NumberTheory.MultipleZeta.Reversal
/-!
Tests for `MathlibExt.NumberTheory.MultipleZeta.Reversal`.
-/


namespace MetaMathlibExt.MultipleZeta

example : oneEntryIndex.reverse.entries = [2] := by
  rfl

example : twoEntryIndex.reverse.entries = [2, 1] := by
  rfl

example : (twoEntryIndex.reverse.entry ⟨0, by decide⟩ : ℕ) = 2 := by
  rfl

example : (twoEntryIndex.reverse.entry ⟨1, by decide⟩ : ℕ) = 1 := by
  rfl

example :
    ((increasingEquivDecreasing twoEntryIndex increasingTupleTwo).1
        ⟨0, by decide⟩ : ℕ) = 2 := by
  rfl

example :
    ((increasingEquivDecreasing twoEntryIndex increasingTupleTwo).1
        ⟨1, by decide⟩ : ℕ) = 1 := by
  rfl

example : oneEntryIndex.reverse.reverse = oneEntryIndex := by
  simp

example : twoEntryIndex.reverse.reverse = twoEntryIndex := by
  simp

example (m : StrictIncreasingTuple oneEntryIndex.depth) :
    increasingSummand oneEntryIndex m =
      strictSummand oneEntryIndex.reverse
        (increasingEquivDecreasing oneEntryIndex m) :=
  increasingSummand_eq_strictSummand_reverse oneEntryIndex m

example (m : StrictIncreasingTuple twoEntryIndex.depth) :
    increasingSummand twoEntryIndex m =
      strictSummand twoEntryIndex.reverse
        (increasingEquivDecreasing twoEntryIndex m) :=
  increasingSummand_eq_strictSummand_reverse twoEntryIndex m

example :
    increasingValue oneEntryIndex oneEntryIndex_admissible =
      strictValue oneEntryIndex.reverse
        (Or.inl
          (oneEntryIndex.isIncreasingAdmissible_iff_reverse_isAdmissible.mp
            oneEntryIndex_admissible)) :=
  increasingValue_eq_strictValue_reverse oneEntryIndex
    oneEntryIndex_admissible

example :
    increasingValue twoEntryIndex twoEntryIndex_admissible =
      strictValue twoEntryIndex.reverse
        (Or.inl
          (twoEntryIndex.isIncreasingAdmissible_iff_reverse_isAdmissible.mp
            twoEntryIndex_admissible)) :=
  increasingValue_eq_strictValue_reverse twoEntryIndex
    twoEntryIndex_admissible

end MetaMathlibExt.MultipleZeta
