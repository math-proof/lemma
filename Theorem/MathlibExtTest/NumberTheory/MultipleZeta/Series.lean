/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Series.lean -/


import Mathlib.Tactic.FinCases
import Def.NumberTheory.MultipleZeta.Series.Part3
import Lemma.Nat.MultipleZeta.Series
import Def.MathlibExtTest.NumberTheory.MultipleZeta.Series


namespace MetaMathlibExt.MultipleZeta

example : Index.empty.entries = [] := by simp

example : Index.empty.weight = 0 := by simp

example : Index.empty.depth = 0 := by simp

example : admissibleIndex.IsAdmissibleOrEmpty := by
  left
  simp [admissibleIndex, Index.IsAdmissible]

example : ¬nonadmissibleIndex.IsAdmissibleOrEmpty := by
  simp [nonadmissibleIndex, Index.IsAdmissibleOrEmpty, Index.IsAdmissible, Index.depth]

example : (admissibleIndex.entry ⟨0, by decide⟩ : ℕ) = 2 :=
  rfl

example : (depthTwoIndex.entry ⟨0, by decide⟩ : ℕ) = 2 :=
  rfl

example : (depthTwoIndex.entry ⟨1, by decide⟩ : ℕ) = 1 :=
  rfl

example : (mOne.1 ⟨0, by decide⟩ : ℕ) = 1 :=
  rfl

example : (mTwo.1 ⟨0, by decide⟩ : ℕ) = 2 :=
  rfl

example : (mTwo.1 ⟨1, by decide⟩ : ℕ) = 1 :=
  rfl

example (m : StrictDecreasingTuple 2) :
    (m.1 ⟨1, by decide⟩ : ℕ) < (m.1 ⟨0, by decide⟩ : ℕ) := by
  have h01 : (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ := by decide
  exact m.2 h01

example (index : Index) (m : StrictDecreasingTuple index.depth) :
    strictSummand index m =
      (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹ :=
  rfl

example : strictValue Index.empty (.inr Index.empty_depth) = 1 := by
  apply strictValue_empty

end MetaMathlibExt.MultipleZeta
