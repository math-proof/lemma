import Lemma.Algebra.GetUnflatten.as.ArraySlice
open Algebra


@[main]
private lemma main
-- given
  (h : i < m)
  (v : List.Vector α (m * n)) :
-- imply
  v.unflatten[i] ≃ v.array_slice (i * n) n := by
-- proof
  let i : Fin m := ⟨i, h⟩
  have := GetUnflatten.as.ArraySlice v i
  simp_all
  assumption


-- created on 2025-05-31
