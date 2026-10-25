/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Finpartition/BasicSetPartition.lean -/


import Def.Combinatorics.Finpartition.BasicSetPartition
import Def.MathlibExtTest.Combinatorics.Finpartition.BasicSetPartition


namespace MetaMathlibExt

example : IsBasicSetPartition 3 oneBlockThree := by
  refine ⟨[groundThree], ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [oneBlockThree, groundThree]
  · simp [groundThree]
  · simp
  · intro i hi hlen
    simp at hlen
    have hi' : i = 1 := by omega
    subst i
    decide

example : ¬ List.Pairwise
    (fun earlier later : Finset ℕ => later.card ≤ earlier.card)
    [{3}, {1, 2}] := by decide

example : ([{1, 3}] : List (Finset ℕ)).foldl (· ∪ ·) ∅ ≠
    Finset.Icc 1 ((([{1, 3}] : List (Finset ℕ)).map Finset.card).sum) := by
  decide

#print axioms IsBasicSetPartition

end MetaMathlibExt
