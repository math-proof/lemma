import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
open Vector


@[main, comm, fin, fin.comm]
private lemma main
-- given
  (h : i < n)
  (v : List.Vector α (n :: s).prod) :
-- imply
  (v.splitAt 1)[i]'(by simp_all) = v.unflatten[i] := by
-- proof
  have := GetSplitAt_1.eq.GetUnflatten v ⟨i, h⟩
  simp_all


-- created on 2025-07-16
