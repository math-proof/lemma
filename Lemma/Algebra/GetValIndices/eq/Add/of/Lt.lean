import stdlib.List.Vector
import Lemma.Algebra.GetIndices.eq.Add
open Algebra


@[main]
private lemma main
  {j n i : ℕ}
-- given
  (h : i < _) :
-- imply
  (List.Vector.indices ⟨j, (n + j : ℕ), 1⟩ (n + j)).val[i] = i + j := by
-- proof
  let slice : Slice := ⟨j, (n + j : ℕ), 1⟩
  have h_nj : slice.length (n + j) = (List.Vector.indices slice (n + j)).val.length := by 
    simp
  rw [← h_nj] at h
  let i : Fin _ := ⟨i, h⟩
  have := GetIndices.eq.Add j n i
  assumption


-- created on 2025-05-28
