import Lemma.Vector.GetUnflatten.as.ArraySlice
open Vector


@[main, cast]
private lemma main
-- given
  (h : i < m)
  (v : List.Vector α (m * n)) :
-- imply
  v.unflatten[i] ≃ v.array_slice (i * n) n := by
-- proof
  have := GetUnflatten.as.ArraySlice v ⟨i, h⟩
  aesop


-- created on 2025-05-31
