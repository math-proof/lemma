import Lemma.Vector.CastDiv.eq.DivCast.of.Eq
import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
import Lemma.Vector.UnflattenDiv.eq.DivUnflatten_Replicate
import Lemma.Vector.SumDiv.eq.DivSum
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Algebra.EraseIdx_0.eq.Drop_1
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.EqGetReplicate
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Algebra.ProdTake.ne.Zero.of.NeProd_0
import Lemma.Algebra.ProdDrop.ne.Zero.of.NeProd_0
open Vector Algebra Logic


@[main]
private lemma main
  [DivisionSemiring α]
  {s : List ℕ}
-- given
  (h : s.prod ≠ 0)
  (x : List.Vector α s.prod)
  (n : α) :
-- imply
  have h : List.Vector α (s.drop 1).prod = List.Vector α (s.eraseIdx 0).prod := by
    simp
  cast h ((x / n).splitAt 1).sum = cast h (x.splitAt 1).sum / n := by
-- proof
  unfold List.Vector.splitAt
  simp
  have h_prod := Prod.eq.MulProdTake__ProdDrop s 1
  rw [CastDiv.eq.DivCast.of.Eq.scalar h_prod]
  rw [UnflattenDiv.eq.DivUnflatten_Replicate]
  have h_ne_take : NeZero (List.take 1 s).prod := ⟨ProdTake.ne.Zero.of.NeProd_0 h 1⟩
  have h_ne_drop : NeZero (List.drop 1 s).prod := ⟨ProdDrop.ne.Zero.of.NeProd_0 h 1⟩
  rw [SumDiv.eq.DivSum (a := List.Vector.replicate (List.drop 1 s).prod n)]
  ext i
  have h_s := Drop_1.eq.EraseIdx_0 s
  have h_s := EqUFnS.of.Eq h_s List.prod
  rw [GetCast.eq.Get.of.Eq.fin h_s]
  rw [GetDiv.eq.DivGetS.fin]
  rw [EqGetReplicate]
  rw [GetDiv.eq.DivGet.fin]
  rw [GetCast.eq.Get.of.Eq.fin h_s]


-- created on 2025-09-21
-- updated on 2025-09-23
