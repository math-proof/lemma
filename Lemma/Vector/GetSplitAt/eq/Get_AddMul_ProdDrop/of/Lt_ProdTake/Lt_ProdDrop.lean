import Lemma.List.AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.List.Prod.eq.MulProdS
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
open Vector List


@[main, fin]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_i : i < (s.take d).prod)
  (h_j : j < (s.drop d).prod)
  (v : List.Vector α s.prod) :
-- imply
  (v.splitAt d)[i, j] = v[i * (s.drop d).prod + j]'(AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop h_i h_j) := by
-- proof
  let i' : Fin (s.take d).prod := ⟨i, h_i⟩
  let j' : Fin (s.drop d).prod := ⟨j, h_j⟩
  have h_i' : i' = i := rfl
  have h_j' : j' = j := rfl
  simp [← h_i', ← h_j']
  apply GetSplitAt.eq.Get_AddMul_ProdDrop


-- created on 2025-07-08
