import Lemma.List.LengthSwap.eq.Length
import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt_Length
import Lemma.List.EqSwap.of.Ge_Length
import Lemma.List.Permute.eq.Permute__Sub.of.Add.ge.SubLength_1
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
open List Bool


@[main]
private lemma main
  {a : List α}
-- given
  (i : Fin a.length)
  (d : ℕ) :
-- imply
  a.permute i (d + 1) = (a.permute i d).swap (i + d) (i + d + 1) := by
-- proof
  have h_length := LengthSwap.eq.Length (a.permute i d) (i + d) (i + d + 1)
  by_cases h : i + d + 1 ≥ a.length
  ·
    rw [EqSwap.of.Ge_Length (by simpa)]
    rw [Permute.eq.Permute__Sub.of.Add.ge.SubLength_1]
    rw [Permute.eq.Permute__Sub.of.Add.ge.SubLength_1 (d := d)]
    repeat grind
  ·
    simp at h
    ext j t
    by_cases h_j : j < a.length
    ·
      simp_all
      apply IffEqS.of.Eq
      rw [GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt_Length (by simp; linarith) (by simp_all) (by simp_all)]
      split_ifs <;>
      ·
        try simp_all
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
        simp [(show a.permute i (↑d + 1) = a.permute i ↑(d + 1) by simp)]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
        repeat grind
    ·
      simp_all


-- created on 2025-06-07
-- updated on 2025-10-26
