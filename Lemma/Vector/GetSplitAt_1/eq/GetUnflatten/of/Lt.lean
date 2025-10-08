import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
open Vector


@[main, comm]
private lemma main
-- given
  (h : i < n)
  (v : List.Vector α (n :: s).prod) :
-- imply
  have : i < ((n :: s).take 1 ).prod := by simp_all
  (v.splitAt 1)[i] = v.unflatten[i] := by
-- proof
  have := GetSplitAt_1.eq.GetUnflatten v ⟨i, h⟩
  simp_all


@[main, comm]
private lemma fin
-- given
  (h : i < n)
  (v : List.Vector α (n :: s).prod) :
-- imply
  have h_i : i < ((n :: s).take 1 ).prod := by simp_all
  (v.splitAt 1).get ⟨i, h_i⟩ = v.unflatten.get ⟨i, h⟩ := by
-- proof
  apply main


-- created on 2025-07-16
