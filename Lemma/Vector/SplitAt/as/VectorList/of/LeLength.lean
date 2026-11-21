import Theorem.Fin.Eq_Fin.of.EqVal
import Theorem.List.EqTake.of.LeLength
import Theorem.List.Drop.eq.Nil.of.LeLength
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetMap.eq.UFnGet
open Fin List Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.SplitAt.as.VectorList.of.LeLength |
| cast | Vector.SplitAt.eq.Cast_VectorList.of.LeLength |
-/
@[path, cast]
private lemma main
  {s : List ℕ}
-- given
  (h : d ≥ s.length)
  (v : List.Vector α s.prod) :
-- imply
  v.splitAt d ≃ v.map (fun x => (⟨[x], by simp [Drop.eq.Nil.of.LeLength h]⟩ : List.Vector α (s.drop d).prod)) := by
-- proof
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_t := t.isLt
    ext j
    rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    simp [Drop.eq.Nil.of.LeLength h]
    have h_j := j.isLt
    simp [Drop.eq.Nil.of.LeLength h] at h_j
    have h_j := Eq_Fin.of.EqVal h_j
    simp [h_j]
    erw [GetMap.eq.UFnGet.fin]
    rfl
  ·
    rw [EqTake.of.LeLength h]


-- created on 2026-07-22
-- updated on 2026-11-21
