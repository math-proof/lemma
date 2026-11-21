import Theorem.List.Prod.eq.MulProdS
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.GetCast.eq.Get.of.Eq
open List Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetSplitAt_1.eq.GetUnflattenCast |
| comm | Vector.GetUnflattenCast.eq.GetSplitAt_1 |
| fin | Vector.GetSplitAt_1.eq.GetUnflattenCast.fin |
| fin.comm | Vector.GetUnflattenCast.eq.GetSplitAt_1.fin |
-/
@[path, comm, fin, fin.comm]
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
    simp [GetElem.getElem]
    erw [GetSplitAt_1.eq.GetUnflatten.fin v ⟨i, by simpa using i.isLt⟩]


-- created on 2025-10-08
-- updated on 2026-11-20
