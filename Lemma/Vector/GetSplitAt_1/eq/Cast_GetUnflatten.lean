import Lemma.List.Prod.eq.MulProdS
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.List.Prod.eq.Foldr
open List Vector


@[main, comm, fin, fin.comm]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (i : Fin (s.take 1).prod) :
-- imply
  (v.splitAt 1)[i] = (cast (congrArg (List.Vector α) (Prod.eq.MulProdS s 1)) v).unflatten[i] := by
-- proof
  match s with
  | [] =>
    simp [List.Vector.splitAt]
  | s₀ :: s =>
    have hi := i.isLt
    simp [GetElem.getElem]
    rw [GetSplitAt_1.eq.GetUnflatten.fin v ⟨i, by simp_all⟩]
    ext j
    simp [GetUnflatten.eq.Get_AddMul.fin]
    rw [GetCast.eq.Get.of.Eq.fin]
    simp [Foldr.eq.Prod]


-- created on 2025-10-08
