import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Notation.Data.Tensor.Permute
open List Tensor


@[path]
private lemma main
-- given
  (h_d : d > 1)
  (h : s.length > 1)
  (X : Tensor α s) :
-- imply
  (X.permuteHead d).length = s[1] := by
-- proof
  have h_min := lt_min h_d h
  have h_take : 1 < (s.take d).length := by simpa using h_min
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [List.getElem_append_left (by simpa using Nat.zero_lt_of_lt h_take), List.getElem_rotate]
    simp [Nat.mod_eq_of_lt h_min]
  ·
    simp
    omega


-- created on 2025-11-03
-- updated on 2026-11-20
