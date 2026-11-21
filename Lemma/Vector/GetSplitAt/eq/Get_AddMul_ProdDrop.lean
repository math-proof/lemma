import Def.Data.Vector.Basic.Part2
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Theorem.List.Prod.eq.MulProdS
import Lemma.Bool.HEq.of.SEq
import Lemma.Vector.Eq.of.Eq_Cast.Eq
open Vector List Bool


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetSplitAt.eq.Get_AddMul_ProdDrop |
| fin | Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.fin |
| val | Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.val |
-/
@[path, fin, val]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (v : List.Vector α s.prod)
  (i : Fin (s.take d).prod)
  (j : Fin (s.drop d).prod) :
-- imply
  have : i * (s.drop d).prod + j < s.prod := by
    rw [Prod.eq.MulProdS s d]
    apply Nat.AddMul.lt.Mul i j
  (v.splitAt d)[i, j] = v[i * (s.drop d).prod + j] := by
-- proof
  intro h_lt
  unfold List.Vector.splitAt
  simp
  have h := Prod.eq.MulProdS s d
  rw [Prod.eq.MulProdS s d] at h_lt
  let v' := cast (by rw [h]) v
  have h_v : v' = cast (by rw [h]) v := rfl
  simp [← h_v]
  have := GetUnflatten.eq.Get_AddMul v' i j
  simp at this
  rw [this]
  congr
  repeat rw [h]
  ·
    apply HEq.of.SEq
    apply Eq.of.Eq_Cast.Eq (by simp)
    assumption
  ·
    simp


-- created on 2025-07-08
-- updated on 2026-11-20
