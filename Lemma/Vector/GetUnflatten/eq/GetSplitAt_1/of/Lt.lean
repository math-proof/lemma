import Lemma.Vector.GetUnflatten.eq.GetSplitAt_1
open Vector


@[main, comm]
private lemma main
-- given
  (h : i < n)
  (v : List.Vector α (n :: s).prod) :
-- imply
  have : i < ((n :: s).take 1 ).prod := by simp_all
  v.unflatten[i] = (v.splitAt 1)[i] := by
-- proof
  have := GetUnflatten.eq.GetSplitAt_1 v ⟨i, h⟩
  simp_all


@[main, comm]
private lemma fin
-- given
  (h : i < n)
  (v : List.Vector α (n :: s).prod) :
-- imply
  have h_i : i < ((n :: s).take 1 ).prod := by simp_all
  v.unflatten.get ⟨i, h⟩ = (v.splitAt 1).get ⟨i, h_i⟩ := by
-- proof
  apply main


-- created on 2025-07-16
