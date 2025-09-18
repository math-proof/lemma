import Lemma.Algebra.AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
import Lemma.Algebra.GetSplitAt.eq.Get_AddMul_ProdDrop
open Algebra


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_i : i < (s.take d).prod)
  (h_j : j < (s.drop d).prod)
  (v : List.Vector α s.prod) :
-- imply
  have := AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop h_i h_j
  (v.splitAt d)[i, j] = v[i * (s.drop d).prod + j] := by
-- proof
  let i' : Fin (s.take d).prod := ⟨i, h_i⟩
  let j' : Fin (s.drop d).prod := ⟨j, h_j⟩
  have h_i' : i' = i := rfl
  have h_j' : j' = j := rfl
  simp [← h_i', ← h_j']
  apply GetSplitAt.eq.Get_AddMul_ProdDrop


@[main]
private lemma fin
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_i : i < (s.take d).prod)
  (h_j : j < (s.drop d).prod)
  (v : List.Vector α s.prod) :
-- imply
  have h_ij := AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop h_i h_j
  ((v.splitAt d).get ⟨i, h_i⟩).get ⟨j, h_j⟩ = v.get ⟨i * (s.drop d).prod + j, h_ij⟩ := by
-- proof
  apply main



-- created on 2025-07-08
