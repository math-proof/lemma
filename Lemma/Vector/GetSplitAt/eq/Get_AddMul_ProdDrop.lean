import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.List.AddMul_ProdDrop.lt.Prod
import Lemma.Logic.HEq.of.SEq
import Lemma.Vector.Eq.of.Eq_Cast.Eq
open Logic Vector List


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (v : List.Vector α s.prod)
  (i : Fin (s.take d).prod)
  (j : Fin (s.drop d).prod) :
-- imply
  have := AddMul_ProdDrop.lt.Prod i j
  (v.splitAt d)[i, j] = v[i * (s.drop d).prod + j] := by
-- proof
  intro h_lt
  unfold List.Vector.splitAt
  simp
  have h := Prod.eq.MulProdTake__ProdDrop s d
  rw [Prod.eq.MulProdTake__ProdDrop s d] at h_lt
  let v' := cast (by rw [h]) v
  have h_v : v' = cast (by rw [h]) v := rfl
  simp [← h_v]
  have := GetUnflatten.eq.Get_AddMul v' i j
  simp at this
  rw [this]
  congr
  ·
    rw [h]
  ·
    rw [h]
  ·
    rw [h]
  ·
    apply HEq.of.SEq
    apply Eq.of.Eq_Cast.Eq (by simp)
    assumption
  ·
    simp


-- created on 2025-07-08
-- updated on 2025-07-09
