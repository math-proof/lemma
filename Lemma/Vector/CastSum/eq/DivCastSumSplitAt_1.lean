import Lemma.Vector.CastDiv.eq.DivCast.of.Eq
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.Vector.Div.eq.Mul_Inv
import Lemma.Vector.UnflattenDiv.eq.DivUnflatten_Replicate
import Lemma.Vector.SumMul.eq.MulSum
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.List.EraseIdx_0.eq.Drop_1
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Vector.EqGetReplicate
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.InvReplicate.eq.ReplicateInv
import Lemma.Algebra.Div.eq.Mul_Inv
open Vector List Algebra Bool


@[main]
private lemma main
  [DivisionSemiring α]
  {s : List ℕ}
-- given
  (x : List.Vector α s.prod)
  (n : α) :
-- imply
  have h : List.Vector α (s.drop 1).prod = List.Vector α (s.eraseIdx 0).prod := by simp
  cast h ((x / n).splitAt 1).sum = cast h (x.splitAt 1).sum / n := by
-- proof
  unfold List.Vector.splitAt
  simp
  have h_prod := Prod.eq.MulProdTake__ProdDrop s 1
  rw [CastDiv.eq.DivCast.of.Eq.scalar h_prod]
  rw [UnflattenDiv.eq.DivUnflatten_Replicate]
  rw [Div.eq.Mul_Inv (A := List.Vector.replicate (List.drop 1 s).prod n)]
  rw [SumMul.eq.MulSum]
  ext i
  have h_s := Drop_1.eq.EraseIdx_0 s
  have h_s := EqUFnS.of.Eq h_s List.prod
  rw [GetCast.eq.Get.of.Eq.fin h_s]
  rw [GetMul.eq.MulGetS.fin]
  rw [InvReplicate.eq.ReplicateInv]
  rw [EqGetReplicate]
  rw [GetDiv.eq.DivGet.fin]
  rw [GetCast.eq.Get.of.Eq.fin h_s]
  rw [Div.eq.Mul_Inv (b := n)]


-- created on 2025-09-21
-- updated on 2025-09-24
