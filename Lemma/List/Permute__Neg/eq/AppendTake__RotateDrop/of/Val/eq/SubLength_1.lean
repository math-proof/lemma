import Lemma.Nat.LtVal
import Lemma.Nat.Eq_Sub_1.of.Val.eq.Sub_1
import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.List.Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.MinSubS.eq.SubMin.of.Ge.Ge
open List Nat Int


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i.val = s.length - 1)
  (d : ℕ) :
-- imply
  s.permute i (-d : ℤ) = s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1) := by
-- proof
  have h_i := LtVal i
  simp_all [Eq_Sub_1.of.Val.eq.Sub_1 h]
  simp_all [Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0 h_i d]
  rw [SubSub.eq.Sub_Add]
  rw [Add.comm (a := 1)]
  norm_num
  congr
  rw [SubMin.eq.MinSubS.of.Ge.Ge]
  simp
  repeat linarith


-- created on 2025-07-14
