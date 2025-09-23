import Lemma.Vector.CastDiv.eq.DivCast.of.Eq
import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
import Lemma.Vector.UnflattenDiv.eq.DivUnflatten_Replicate
import Lemma.Vector.SumDiv.eq.DivSum
import Lemma.Algebra.GetCast.eq.Get.of.Eq
open Vector Algebra


@[main]
private lemma main
  [DivisionSemiring α]
  {s : List ℕ}
-- given
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
  have h_ne_take : (List.take 1 s).prod ≠ 0 := by
    simp
    sorry
  have h_ne_drop : (List.drop 1 s).prod ≠ 0 := by
    simp
    sorry
  have h_ne_take : NeZero (List.take 1 s).prod := ⟨h_ne_take⟩
  have h_ne_drop : NeZero (List.drop 1 s).prod := ⟨h_ne_drop⟩
  rw [SumDiv.eq.DivSum (a := List.Vector.replicate (List.drop 1 s).prod n)]
  -- simp [HDiv.hDiv]
  ext i
  rw [GetCast.eq.Get.of.Eq.fin]
  .
    sorry
  .
    sorry


-- created on 2025-09-21
-- updated on 2025-09-22
