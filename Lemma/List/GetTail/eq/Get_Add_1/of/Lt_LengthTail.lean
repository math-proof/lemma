import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : i < s.tail.length) :
-- imply
  have : i + 1 < s.length := by
    simp at h
    omega
  s.tail[i] = s[i + 1] := by
-- proof
  intro h_i
  apply GetTail.eq.Get_Add_1.of.Lt_SubLength_1
  omega


@[main]
private lemma fin
  {s : List α}
-- given
  (h : i < s.tail.length) :
-- imply
  have h_i : i + 1 < s.length := by
    simp at h
    omega
  s.tail.get ⟨i, h⟩ = s.get ⟨i + 1, h_i⟩ := by
-- proof
  apply main h


-- created on 2025-10-10
