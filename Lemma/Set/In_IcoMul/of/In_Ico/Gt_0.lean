import Lemma.Set.Ge.Le_Sub_1.of.In_Ico
import Lemma.Set.In_Ico.is.Le.Lt
import Lemma.Nat.LeMulS.of.Le.Gt_0
import Lemma.Nat.Lt_Add_1.of.Le
open Set Nat


@[main]
private lemma main
  [IntegerRing α]
  {x a b d : α}
-- given
  (h_d : d > 0)
  (h : x ∈ Ico a b) :
-- imply
  d * x ∈ Ico (a * d) (d * (b - 1) + 1) := by
-- proof
  obtain ⟨h_ge, h_le⟩ := Ge.Le_Sub_1.of.In_Ico h
  apply In_Ico.of.Le.Lt
  · simpa [mul_comm] using LeMulS.of.Le.Gt_0 h_ge h_d
  · have h_mul_le := LeMulS.of.Le.Gt_0 h_le h_d
    simpa [mul_comm] using Lt_Add_1.of.Le h_mul_le


-- created on 2018-05-26
