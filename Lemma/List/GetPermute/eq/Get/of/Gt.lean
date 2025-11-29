import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.GetPermute.eq.Ite.of.GtLength.GtLength
open List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {j : ℕ}
-- given
  (h : i > j)
  (d : ℕ) :
-- imply
  (s.permute i d)[j]'(by simp; omega) = s[j] := by
-- proof
  by_cases h_d : i + d < s.length
  .
    rw [GetPermute.eq.Ite.of.GtLength.GtLength h_d (by omega)]
    split_ifs
    repeat rfl
  .
    simp at h_d
    have h_d : i + d ≥ s.length - 1 := by omega
    simp [EqPermuteS.of.Add.ge.SubLength_1 h_d]
    rw [GetPermute.eq.Ite.of.GtLength.GtLength (by omega) (by omega)]
    split_ifs
    repeat rfl


-- created on 2025-11-02
