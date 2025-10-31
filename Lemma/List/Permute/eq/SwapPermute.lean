import Lemma.List.LengthSwap.eq.Length
import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt_Length
import Lemma.List.EqSwap.of.Ge_Length
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
open List Bool


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  s.permute i (d + 1) = (s.permute i d).swap (i + d) (i + d + 1) := by
-- proof
  have h_length := LengthSwap.eq.Length (s.permute i d) (i + d) (i + d + 1)
  by_cases h : i + d + 1 ≥ s.length
  ·
    rw [EqSwap.of.Ge_Length (by simpa)]
    rw [EqPermuteS.of.Add.ge.SubLength_1]
    rw [EqPermuteS.of.Add.ge.SubLength_1.int]
    repeat grind
  ·
    simp at h
    ext j t
    by_cases h_j : j < s.length
    ·
      simp_all
      apply IffEqS.of.Eq
      rw [GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt_Length (by simp; linarith) (by simp_all) (by simp_all)]
      split_ifs <;>
      ·
        try simp_all
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
        simp [show s.permute i (d + 1) = s.permute i ↑(d + 1) by simp]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
        repeat grind
    ·
      simp_all


-- created on 2025-06-07
-- updated on 2025-10-26
