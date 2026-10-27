import Instance.Data.Holor.Tensor.Part2
open List Tensor


@[path]
private lemma main
-- given
  (h_s : s.length > 1)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  (X.get ⟨i, by simpa [Length.eq.Get_0.of.GtLength h_s X]⟩).length = s[1] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    grind
  ·
    simp
    omega


-- created on 2025-11-01
