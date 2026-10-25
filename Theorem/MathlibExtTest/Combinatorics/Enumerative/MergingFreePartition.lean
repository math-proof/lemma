/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MergingFreePartition.lean -/


import Def.Combinatorics.Enumerative.MergingFreePartition
import Mathlib.Tactic


namespace MetaMathlibExt

example : IsMergingFreePartition 0 [] := by
  simp [IsMergingFreePartition]

example : IsMergingFreePartition 1 [{0}] := by
  simp [IsMergingFreePartition]

/-- The adjacent blocks `{0, 2}` and `{1, 3}` overlap in range without
overlapping as sets, so their maximum/minimum inequality is merging-free. -/
example : IsMergingFreePartition 4 [{0, 2}, {1, 3}] := by
  classical
  have hcover : ∀ x : Fin 4, (x = 0 ∨ x = 2) ∨ x = 1 ∨ x = 3 := by
    intro x
    fin_cases x <;> simp
  simpa [IsMergingFreePartition] using hcover

/-- Separating the same ground set into consecutive intervals is not
merging-free because `max {0, 1} ≤ min {2, 3}`. -/
example : ¬ IsMergingFreePartition 4 [{0, 1}, {2, 3}] := by
  classical
  simp [IsMergingFreePartition]

#print axioms IsMergingFreePartition

end MetaMathlibExt
