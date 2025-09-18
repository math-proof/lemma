import Lemma.Algebra.NegSucc.eq.NegCoeAdd_1
import Lemma.Algebra.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.Algebra.EqMin.of.Lt
import Lemma.Algebra.LtAdd.of.Lt_Sub
import Lemma.Algebra.ProdAppend.eq.MulProdS
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Algebra.AppendAppend.eq.Append_Append
import Lemma.Algebra.EqAppendS.of.Eq
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Algebra.MinAddS.eq.AddMin
import Lemma.Algebra.Val.lt.Sub_1.of.Val.ne.Sub_1
import Lemma.Algebra.Add
import Lemma.Algebra.EqSubAdd
open Algebra Logic


@[main]
private lemma main
  [Monoid α]
  {s : List α}
  {d : Fin s.length}
-- given
  (h : d.val ≠ s.length - 1)
  (k : ℕ) :
-- imply
  (s.permute d (-k : ℤ)).prod = ((s.take (d + 1)).take ((s.take (d + 1)).length - (k + 1)) ++ ((s.take (d + 1)).drop ((s.take (d + 1)).length - (k + 1))).rotate ((k + 1) ⊓ (s.take (d + 1)).length - 1)).prod * (s.drop (d + 1)).prod := by
-- proof
  have h := Val.lt.Sub_1.of.Val.ne.Sub_1 h
  simp_all
  rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
  simp_all
  rw [EqMin.of.Lt (LtAdd.of.Lt_Sub.nat h)]
  repeat rw [MulProdS.eq.ProdAppend]
  apply EqUFnS.of.Eq _ List.prod
  rw [Append_Append.eq.AppendAppend]
  apply EqAppendS.of.Eq
  rw [Add.comm (a := k)]
  rw [Sub_Add.eq.SubSub.nat]
  simp [EqSubAdd]
  congr
  rw [Add.comm (b := k)]
  rw [MinAddS.eq.AddMin]
  simp


-- created on 2025-07-14
