import Lemma.Nat.Gt_0
import Lemma.Int.AddToNat.eq.ToNatAdd.of.Gt_0
import Lemma.Algebra.EqMax.of.Gt
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
open Algebra List Int Nat


@[main]
private lemma main
  {a : List α}
  {d : Fin a.length}
-- given
  (h_d : d.val = 0)
  (h_i : i > 0) :
-- imply
  a.permute d i = (a.take (i + 1).toNat).rotate 1 ++ a.drop (i + 1).toNat := by
-- proof
  have := Permute.eq.AppendRotateTake___Drop.of.EqVal_0 h_d i.toNat
  rw [AddToNat.eq.ToNatAdd.of.Gt_0 (by linarith)] at this
  simp [EqMax.of.Gt h_i] at this
  rw [← this]


-- created on 2025-07-14
