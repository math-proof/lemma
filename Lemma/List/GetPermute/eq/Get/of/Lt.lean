import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
open List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {j : ℕ}
-- given
  (h : j < i)
  (d : ℕ) :
-- imply
  (s.permute i d)[j]'(by simp; omega) = s[j] := by
-- proof
  by_cases h_d : i + d < s.length
  .
    rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length h_d (by omega)]
    split_ifs
    rfl
  .
    simp at h_d
    have h_d : i + d ≥ s.length - 1 := by omega
    simp [EqPermuteS.of.Add.ge.SubLength_1 h_d]
    rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by omega) (by omega)]
    split_ifs
    rfl


-- created on 2025-11-02
