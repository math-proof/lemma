/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/Overpartition.lean -/


import Def.Combinatorics.Enumerative.Partition.Overpartition
import Lemma.Nat.Enumerative.Partition.Overpartition
import Def.MathlibExtTest.Combinatorics.Enumerative.Partition.Overpartition


namespace Nat.Overpartition

-- Selective overlining, membership, positivity, and the `full` constructor.
example :
    overpartition14.IsOverlined 5 ∧ overpartition14.IsOverlined 1 ∧
      ¬overpartition14.IsOverlined 3 ∧ 5 ∈ overpartition14.toPartition.parts ∧
        (0 : ℕ) < 5 ∧ (full partition14).IsOverlined 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [overpartition14, IsOverlined]
  · simp [overpartition14, IsOverlined]
  · simp [overpartition14, IsOverlined]
  · decide
  · exact overpartition14.isOverlined_pos (by simp [overpartition14, IsOverlined])
  · exact (isOverlined_full partition14 3).mpr (by decide)

-- Empty and full constructors have the expected underlying partition and overline sets.
example : (ofPartition partition14).overlines = ∅ := by
  simp

example : (full partition14).overlines = partition14.parts.toFinset := by
  simp

example (a : ℕ) : ¬ (ofPartition partition14).IsOverlined a := by
  simp

-- Zero boundary: the unique overpartition of `0` has empty overlines and any two coincide.
example (O : Nat.Overpartition 0) : O.overlines = ∅ :=
  overlines_eq_empty_of_zero

example (O₁ O₂ : Nat.Overpartition 0) : O₁ = O₂ :=
  eq_of_zero O₁ O₂

end Nat.Overpartition
