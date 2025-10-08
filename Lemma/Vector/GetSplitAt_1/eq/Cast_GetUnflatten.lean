import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.Vector.GetUnflatten.eq.GetSplitAt_1
import Lemma.Nat.LtVal
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.GetCast.eq.Get.of.Eq
open List Vector Nat


@[main, comm]
private lemma fin
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (i : Fin (s.take 1).prod) :
-- imply
  (cast (congrArg (List.Vector α) (Prod.eq.MulProdTake__ProdDrop s 1)) v).unflatten.get i = (v.splitAt 1).get i := by
-- proof
  match s with
  | [] =>
    simp [List.Vector.splitAt]
  | s₀ :: s =>
    have hi := LtVal i
    rw [GetSplitAt_1.eq.GetUnflatten.fin v ⟨i, by simp_all⟩]
    ext j
    repeat rw [GetUnflatten.eq.Get_AddMul.fin]
    simp [GetCast.eq.Get.of.Eq.fin]


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (i : Fin (s.take 1).prod) :
-- imply
  (cast (congrArg (List.Vector α) (Prod.eq.MulProdTake__ProdDrop s 1)) v).unflatten[i] = (v.splitAt 1)[i] := by
-- proof
  apply fin


-- created on 2025-10-08
