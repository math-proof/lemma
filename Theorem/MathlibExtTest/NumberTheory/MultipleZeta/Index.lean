/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Index.lean -/


import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index
import Def.MathlibExtTest.NumberTheory.MultipleZeta.Index


namespace MetaMathlibExt.MultipleZeta

example : emptyIndex.entries = [] := rfl

example : emptyIndex.depth = 0 := rfl

example : emptyIndex.height = 0 := rfl

example : ¬emptyIndex.IsAdmissible := by
  simp [emptyIndex, Index.IsAdmissible]

example : ¬oneIndex.IsAdmissible := by
  simp [oneIndex, Index.IsAdmissible]

example : twoIndex.IsAdmissible := by
  simp [twoIndex, Index.IsAdmissible]

example (index : Index) :
    index.IsAdmissible ↔ IsAdmissible index.entries :=
  index.isAdmissible_iff

example : ¬IsAdmissible [] := by
  simp

example : ¬IsAdmissible [1] := by
  simp [IsAdmissible]

example : IsAdmissible [2] := by
  simp [IsAdmissible]

example : IsAdmissible [2, 1] := by
  simp [IsAdmissible]

example : ¬IsAdmissible [2, 0] := by
  simp [IsAdmissible]

example : heightExample.entries = [1, 2, 2] := rfl

example : heightExample.weight = 5 := rfl

example : heightExample.depth = 3 := rfl

example : heightExample.height = 2 := rfl

example (index : Index) : index.entries.sum = index.weight := by
  rcases index with ⟨weight, composition⟩
  exact composition.blocks_sum

end MetaMathlibExt.MultipleZeta
