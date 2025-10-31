import Lemma.Nat.Gt_0
import Lemma.Int.AddToNat.eq.ToNatAdd.of.Gt_0
import Lemma.Nat.EqMax.of.Gt
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
open List Int Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h_i : i.val = 0)
  (h_d : d > 0) :
-- imply
  s.permute i d = (s.take (d + 1).toNat).rotate 1 ++ s.drop (d + 1).toNat := by
-- proof
  have := Permute.eq.AppendRotateTake___Drop.of.EqVal_0 h_i d.toNat
  rw [AddToNat.eq.ToNatAdd.of.Gt_0 (by linarith)] at this
  simp [EqMax.of.Gt h_d] at this
  rw [← this]


-- created on 2025-07-14
