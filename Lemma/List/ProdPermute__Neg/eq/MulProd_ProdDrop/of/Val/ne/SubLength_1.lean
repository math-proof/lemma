import Lemma.Int.NegSucc.eq.NegCoeAdd_1
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqAppendS.of.Eq
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.MinAddS.eq.AddMin
import Lemma.Nat.Val.lt.Sub_1.of.Val.ne.Sub_1
import Lemma.Nat.Add
import Lemma.Nat.EqSubAdd
open List Bool Nat Int


@[main]
private lemma main
  [Monoid α]
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i.val ≠ s.length - 1)
  (d : ℕ) :
-- imply
  (s.permute i (-d : ℤ)).prod = ((s.take (i + 1)).take ((s.take (i + 1)).length - (d + 1)) ++ ((s.take (i + 1)).drop ((s.take (i + 1)).length - (d + 1))).rotate ((d + 1) ⊓ (s.take (i + 1)).length - 1)).prod * (s.drop (i + 1)).prod := by
-- proof
  have h := Val.lt.Sub_1.of.Val.ne.Sub_1 h
  simp_all
  rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
  simp_all
  rw [EqMin.of.Lt (LtAdd.of.Lt_Sub h)]
  repeat rw [MulProdS.eq.ProdAppend]
  apply EqUFnS.of.Eq _ List.prod
  rw [Append_Append.eq.AppendAppend]
  apply EqAppendS.of.Eq
  rw [Add.comm (a := d)]
  rw [Sub_Add.eq.SubSub]
  congr
  rw [Add.comm (b := d)]
  rw [MinAddS.eq.AddMin]
  simp


-- created on 2025-07-14
