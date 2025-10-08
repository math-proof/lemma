import Lemma.Nat.LtVal
import Lemma.Algebra.Eq_Sub_1.of.Val.eq.Sub_1
import Lemma.Algebra.NegSucc.eq.NegAdd_1
import Lemma.List.Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Nat.Add
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Algebra.MinSubS.eq.SubMin.of.Ge.Ge
open Algebra List Nat


@[main]
private lemma main
  {s : List α}
  {d : Fin s.length}
-- given
  (h : d.val = s.length - 1)
  (k : ℕ) :
-- imply
  s.permute d (-k : ℤ) = s.take (s.length - (k + 1)) ++ (s.drop (s.length - (k + 1))).rotate ((k + 1) ⊓ s.length - 1) := by
-- proof
  have h_d := LtVal d
  simp_all [Eq_Sub_1.of.Val.eq.Sub_1 h]
  simp_all [Permute_SubLength_0.eq.AppendRotateTake___Drop.of.GtLength_0 h_d k]
  rw [SubSub.eq.Sub_Add.nat]
  rw [Add.comm (a := 1)]
  norm_num
  congr
  rw [← MinSubS.eq.SubMin.of.Ge.Ge]
  simp
  .
    linarith
  .
    linarith


-- created on 2025-07-14
