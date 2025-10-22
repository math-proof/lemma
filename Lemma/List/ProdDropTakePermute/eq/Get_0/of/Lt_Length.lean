import Lemma.List.DropTakePermute.eq.ListGet_0.of.Lt_Length
open List


@[main]
private lemma main
  [MulOneClass α]
  {s : List α}
-- given
  (h : d < s.length) :
-- imply
  (((s.permute ⟨0, by linarith⟩ d).take (d + 1)).drop d).prod = s[0] := by
-- proof
  simp [DropTakePermute.eq.ListGet_0.of.Lt_Length h]


-- created on 2025-10-22
