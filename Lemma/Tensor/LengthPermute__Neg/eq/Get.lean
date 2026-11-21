import Theorem.List.GetPermute__Neg.eq.Ite.of.GtLength
import Notation.Data.Tensor.Permute
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open List Tensor


@[path]
private lemma main
-- given
  (X : Tensor α s)
  (d : Fin s.length) :
-- imply
  (X.permute d (-d)).length = s[d] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [GetPermute__Neg.eq.Ite.of.GtLength (Nat.zero_lt_of_lt d.isLt) d d.val]
    simp
  ·
    simp
    linarith [d.isLt]


-- created on 2025-11-23
-- updated on 2026-11-20
